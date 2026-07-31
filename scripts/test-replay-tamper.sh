#!/usr/bin/env bash
# Focused replay rejection gates for scripts/replay.sh.
#
# Proves policy tampering fails before checker execution, then exercises both
# walking-skeleton identity constraints with hash-invalid scratch bundles:
# the schema identity is fixed, and the bundle directory must match it.
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
replay="$repo_root/scripts/replay.sh"
source_bundle="$repo_root/bundles/walking-skeleton"

tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/lara-replay-tamper.XXXXXX")"
trap 'rm -rf "$tmp_root"' EXIT HUP INT TERM
bundle="$tmp_root/walking-skeleton"
cp -R "$source_bundle" "$bundle"
printf '\n# doctored trusted input\n' >>"$bundle/empirical-v1.policy.lara"

marker="$tmp_root/checker-was-invoked"
fake_checker="$tmp_root/fake-lara"
cat >"$fake_checker" <<'FAKE'
#!/usr/bin/env bash
: >"$LARA_FAKE_MARKER"
exit 99
FAKE
chmod +x "$fake_checker"

stdout="$tmp_root/replay.stdout"
stderr="$tmp_root/replay.stderr"

expect_schema_failure() {
  test_bundle="$1"
  expected_error="$2"
  label="$3"

  rm -f "$marker"
  if LARA_FAKE_MARKER="$marker" "$replay" "$test_bundle" "$fake_checker" >"$stdout" 2>"$stderr"; then
    echo "FAIL: $label was accepted" >&2
    exit 1
  else
    replay_exit=$?
  fi

  if [ "$replay_exit" -ne 2 ]; then
    echo "FAIL: $label exited $replay_exit, expected 2" >&2
    cat "$stderr" >&2
    exit 1
  fi

  error_text="$(cat "$stderr")"
  if [ "$error_text" != "$expected_error" ]; then
    echo "FAIL: $label did not report only the expected manifest error" >&2
    cat "$stderr" >&2
    exit 1
  fi

  if [ -e "$marker" ]; then
    echo "FAIL: checker ran before manifest validation for $label" >&2
    exit 1
  fi

  if [ -s "$stdout" ]; then
    echo "FAIL: replay wrote unexpected stdout for $label" >&2
    cat "$stdout" >&2
    exit 1
  fi
}

if LARA_FAKE_MARKER="$marker" "$replay" "$bundle" "$fake_checker" >"$stdout" 2>"$stderr"; then
  echo "FAIL: tampered trusted input was accepted" >&2
  exit 1
else
  replay_exit=$?
fi

if [ "$replay_exit" -ne 1 ]; then
  echo "FAIL: hash mismatch exited $replay_exit, expected 1" >&2
  cat "$stderr" >&2
  exit 1
fi

error_text="$(cat "$stderr")"
case "$error_text" in
  *"ERROR: trusted input hash mismatch"*) ;;
  *)
    echo "FAIL: replay did not report the trusted-input hash mismatch" >&2
    cat "$stderr" >&2
    exit 1
    ;;
esac

if [ -e "$marker" ]; then
  echo "FAIL: checker ran before trusted-input integrity validation" >&2
  exit 1
fi

if [ -s "$stdout" ]; then
  echo "FAIL: replay wrote unexpected stdout on integrity failure" >&2
  cat "$stdout" >&2
  exit 1
fi

arbitrary_bundle="$tmp_root/arbitrary-skeleton"
cp -R "$source_bundle" "$arbitrary_bundle"
python3 - "$arbitrary_bundle/manifest.json" <<'PY'
import json
import sys
from pathlib import Path

path = Path(sys.argv[1])
manifest = json.loads(path.read_text(encoding="ascii"))
manifest["skeleton"] = "arbitrary-skeleton"
path.write_text(
    json.dumps(manifest, sort_keys=True, indent=2, ensure_ascii=True) + "\n",
    encoding="ascii",
)
PY
printf '\n# schema-before-hash probe\n' >>"$arbitrary_bundle/empirical-v1.policy.lara"
expect_schema_failure \
  "$arbitrary_bundle" \
  "ERROR: manifest skeleton must be 'walking-skeleton'" \
  "renamed arbitrary skeleton"

renamed_bundle="$tmp_root/renamed-walking-skeleton"
cp -R "$source_bundle" "$renamed_bundle"
printf '\n# schema-before-hash probe\n' >>"$renamed_bundle/empirical-v1.policy.lara"
expect_schema_failure \
  "$renamed_bundle" \
  "ERROR: manifest skeleton 'walking-skeleton' does not match bundle directory 'renamed-walking-skeleton'" \
  "walking-skeleton manifest in renamed directory"

echo "PASS: trusted-input and manifest identity tampering fail before checker execution"

# Artifact-identity drift: change only the artifact digest in emitted.lara
# (emitted.lara is untrusted, so manifest validation succeeds; the checker runs,
# and verdict-carried replay identity detects drift).
drift_bundle="$tmp_root/walking-skeleton"
rm -rf "$drift_bundle"
cp -R "$source_bundle" "$drift_bundle"
sed -i.bak 's/\(^artifact kv_quant_suite at sha256:5ca1e\)\(.*\)/\1-drift\2/' "$drift_bundle/emitted.lara"
rm -f "$drift_bundle/emitted.lara.bak"
rm -f "$marker"
drift_stderr="$tmp_root/drift.stderr"
drift_stdout="$tmp_root/drift.stdout"
set +e
"$replay" "$drift_bundle" >"$drift_stdout" 2>"$drift_stderr"
drift_exit=$?
set -e
if [ "$drift_exit" -eq 0 ]; then
  echo "FAIL: artifact-drift replay was accepted (exit 0)" >&2
  exit 1
fi
if [ "$drift_exit" -ne 1 ]; then
  echo "FAIL: artifact-drift replay exited $drift_exit, expected 1" >&2
  cat "$drift_stderr" >&2
  exit 1
fi
if ! grep -q "replay verdict bytes differ" "$drift_stderr"; then
  echo "FAIL: artifact-drift replay did not report verdict byte mismatch" >&2
  cat "$drift_stderr" >&2
  exit 1
fi
if [ -s "$drift_stdout" ]; then
  echo "FAIL: artifact-drift replay wrote unexpected stdout" >&2
  cat "$drift_stdout" >&2
  exit 1
fi
echo "PASS: artifact-digest drift invokes checker and fails on verdict byte mismatch"
