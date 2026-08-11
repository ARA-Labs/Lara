#!/usr/bin/env bash
# End-to-end M4b golden: source.yaml -> PEP 723 elaborator -> machine-produced
# .lara -> unchanged lara checker -> frozen verdict. It also proves producer
# determinism, policy-copy authenticity, and bundle wire-anchor freshness.
#
# From the repository root, after building lara:
#   bash test/walking-skeleton-golden.sh "$(cabal list-bin exe:lara)"
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
committed_bundle="$repo_root/bundles/walking-skeleton"
canonical_policy="$repo_root/examples/E1/empirical-v1.policy.lara"

if [ "$#" -ne 1 ]; then
  echo "usage: bash test/walking-skeleton-golden.sh LARA_BIN" >&2
  exit 2
fi
if ! command -v uv >/dev/null 2>&1; then
  echo "ERROR: uv is required" >&2
  exit 2
fi

lara_arg="$1"
case "$lara_arg" in
  /*) ;;
  *) lara_arg="$(pwd)/$lara_arg" ;;
esac
if [ ! -f "$lara_arg" ] || [ ! -x "$lara_arg" ]; then
  echo "ERROR: lara binary is not executable: $lara_arg" >&2
  exit 2
fi
lara_bin="$(cd "$(dirname "$lara_arg")" && pwd -P)/$(basename "$lara_arg")"

tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/lara-walking-skeleton.XXXXXX")"
trap 'rm -rf "$tmp_root"' EXIT HUP INT TERM
scratch_bundle="$tmp_root/walking-skeleton"
mkdir "$scratch_bundle"
# Deliberately seed only the human-authored research source. Every certificate,
# policy copy, provenance record, and wire anchor below must be produced afresh.
cp "$committed_bundle/source.yaml" "$scratch_bundle/source.yaml"

uv run --no-project "$repo_root/elaborator/elaborate.py" "$scratch_bundle"

assert_same() {
  expected="$1"
  actual="$2"
  description="$3"
  if ! cmp -s "$expected" "$actual"; then
    echo "ERROR: $description differs byte-for-byte" >&2
    cmp "$expected" "$actual" >&2 || :
    exit 1
  fi
}

assert_same \
  "$committed_bundle/emitted.lara" \
  "$scratch_bundle/emitted.lara" \
  "fresh emitted.lara and committed golden"
assert_same \
  "$committed_bundle/provenance.json" \
  "$scratch_bundle/provenance.json" \
  "fresh provenance.json and committed golden"
assert_same \
  "$canonical_policy" \
  "$scratch_bundle/empirical-v1.policy.lara" \
  "fresh policy copy and canonical examples/E1 policy"
assert_same \
  "$committed_bundle/empirical-v1.policy.lara" \
  "$scratch_bundle/empirical-v1.policy.lara" \
  "fresh policy copy and committed bundle policy"

# Re-derive the machine-produced wire anchor in scratch. Never rewrite the
# committed anchor merely to make the differential corpus self-consistent.
(
  cd "$repo_root"
  cabal exec -- runghc scripts/gen-worked-examples.hs \
    --bundle "$scratch_bundle"
)
assert_same \
  "$committed_bundle/emitted.core.sexp" \
  "$scratch_bundle/emitted.core.sexp" \
  "fresh bundle wire anchor and committed emitted.core.sexp"

expected_exit="$(python3 - "$committed_bundle/manifest.json" <<'PY'
import json
import sys

with open(sys.argv[1], "r", encoding="utf-8") as handle:
    manifest = json.load(handle)
value = manifest["frozen-verdict"]["exit-code"]
if type(value) is not int or value not in (0, 1, 2):
    raise SystemExit("invalid manifest frozen-verdict.exit-code")
print(value)
PY
)"

checker_stdout="$tmp_root/checker.stdout"
checker_stderr="$tmp_root/checker.stderr"
set +e
(
  cd "$scratch_bundle"
  "$lara_bin" check emitted.lara
) >"$checker_stdout" 2>"$checker_stderr"
checker_exit=$?
set -e

failed=0
if ! cmp -s "$committed_bundle/verdict.txt" "$checker_stdout"; then
  echo "ERROR: checker stdout differs from committed verdict.txt" >&2
  cmp "$committed_bundle/verdict.txt" "$checker_stdout" >&2 || :
  failed=1
fi
if [ "$checker_exit" -ne "$expected_exit" ]; then
  echo "ERROR: checker exit differs: expected $expected_exit, got $checker_exit" >&2
  failed=1
fi

# Independent replay + B0 §9 semantic oracle: the verdict carries the source
# replay identity and accepts with openweb justified, python_code defeated, and
# mobile_edge gap. This exact expected verdict keeps a self-consistent
# substitution of verdict.txt + manifest from blessing a change.
semantic_oracle="$tmp_root/semantic-oracle.txt"
cat >"$semantic_oracle" <<'EOF'
(verdict (replay-id (core lara-core@0.2) (policy empirical-v1) (backends (backend nd 1)) (theories) (artifact sha256:5ca1e...)) accept (labels (0 in) (1 out) (2 in) (3 in)) (edges (2 1) (3 1)) (statuses (status (atom improves (con kv_quant) (con latency) (con openweb)) justified) (status (atom improves (con kv_quant) (con latency) (con python_code)) defeated) (status (atom improves (con kv_quant) (con latency) (con mobile_edge)) gap)))
EOF
if ! cmp -s "$semantic_oracle" "$checker_stdout"; then
  echo "ERROR: checker stdout does not match the independent B0 section 9 oracle" >&2
  cmp "$semantic_oracle" "$checker_stdout" >&2 || :
  failed=1
fi

if [ "$failed" -ne 0 ]; then
  if [ -s "$checker_stderr" ]; then
    echo "checker stderr:" >&2
    cat "$checker_stderr" >&2
  fi
  exit 1
fi

echo "PASS: walking-skeleton source elaborates deterministically to the B0 oracle (exit $checker_exit)"
