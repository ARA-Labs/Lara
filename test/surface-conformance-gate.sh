#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

golden="$tmp_dir/surface-conformance.golden"
cp "$repo_root/test/surface-conformance.golden" "$golden"

# Update must install a separately written same-directory candidate via rename,
# not overwrite the existing inode in place.
sed -i '2s/ca29927052f38c45/0000000000000000/' "$golden"
old_inode="$(stat -c %i "$golden")"
SURFACE_CONFORMANCE_GOLDEN="$golden" \
  "$repo_root/scripts/check-surface-conformance.sh" --update >/dev/null
new_inode="$(stat -c %i "$golden")"
[ "$old_inode" != "$new_inode" ] || {
  echo "surface gate test: update overwrote the golden inode in place" >&2
  exit 1
}
cmp "$repo_root/test/surface-conformance.golden" "$golden"
if compgen -G "$tmp_dir/.surface-conformance.golden.tmp.*" >/dev/null; then
  echo "surface gate test: successful update left a candidate" >&2
  exit 1
fi

# Check mode must not replace or write the selected golden.
before="$(stat -c '%i:%Y:%s' "$golden"):$(sha256sum "$golden" | cut -d' ' -f1)"
SURFACE_CONFORMANCE_GOLDEN="$golden" \
  "$repo_root/scripts/check-surface-conformance.sh" >/dev/null
after="$(stat -c '%i:%Y:%s' "$golden"):$(sha256sum "$golden" | cut -d' ' -f1)"
[ "$before" = "$after" ] || {
  echo "surface gate test: check mode wrote the golden" >&2
  exit 1
}

# An emitter disagreement must refuse an update before creating or replacing
# the selected golden.
before_disagreement="$(stat -c '%i:%Y:%s' "$golden"):$(sha256sum "$golden" | cut -d' ' -f1)"
disagreement_log="$tmp_dir/emitter-disagreement.log"
set +e
SURFACE_CONFORMANCE_GOLDEN="$golden" \
SURFACE_CONFORMANCE_TEST_MUTATE_HASKELL_OUTPUT=1 \
  "$repo_root/scripts/check-surface-conformance.sh" --update >"$disagreement_log" 2>&1
disagreement_status=$?
set -e
[ "$disagreement_status" -eq 1 ] || {
  echo "surface gate test: emitter disagreement did not exit 1" >&2
  cat "$disagreement_log" >&2
  exit 1
}
grep -Fxq 'surface conformance: FAIL: emitters differ; refusing golden update' \
  "$disagreement_log" || {
  echo "surface gate test: emitter disagreement missed the refusal path" >&2
  cat "$disagreement_log" >&2
  exit 1
}
after_disagreement="$(stat -c '%i:%Y:%s' "$golden"):$(sha256sum "$golden" | cut -d' ' -f1)"
[ "$before_disagreement" = "$after_disagreement" ] || {
  echo "surface gate test: emitter disagreement changed the golden" >&2
  cat "$disagreement_log" >&2
  exit 1
}
if compgen -G "$tmp_dir/.surface-conformance.golden.tmp.*" >/dev/null; then
  echo "surface gate test: emitter disagreement left a candidate" >&2
  exit 1
fi

# A failure after candidate creation but before rename must preserve the old
# golden and remove the candidate through the ordinary trap cleanup.
before_failure="$(sha256sum "$golden" | cut -d' ' -f1)"
failure_log="$tmp_dir/pre-rename-failure.log"
set +e
SURFACE_CONFORMANCE_GOLDEN="$golden" \
SURFACE_CONFORMANCE_TEST_FAIL_BEFORE_RENAME=1 \
  "$repo_root/scripts/check-surface-conformance.sh" --update >"$failure_log" 2>&1
failure_status=$?
set -e
[ "$failure_status" -eq 1 ] || {
  echo "surface gate test: injected pre-rename failure did not exit 1" >&2
  cat "$failure_log" >&2
  exit 1
}
grep -Fxq 'surface conformance: FAIL: injected pre-rename failure' \
  "$failure_log" || {
  echo "surface gate test: injected failure did not reach the pre-rename path" >&2
  cat "$failure_log" >&2
  exit 1
}
after_failure="$(sha256sum "$golden" | cut -d' ' -f1)"
[ "$before_failure" = "$after_failure" ] || {
  echo "surface gate test: failed update changed the golden" >&2
  exit 1
}
if compgen -G "$tmp_dir/.surface-conformance.golden.tmp.*" >/dev/null; then
  echo "surface gate test: failed update left a candidate" >&2
  exit 1
fi

echo "surface gate test: PASS"
