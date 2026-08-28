#!/usr/bin/env bash
set -euo pipefail

# Rebuild the Lean oracle, emit its Haskell literal, and compare that literal
# with the checked-in conformance table. This prevents a stale transcript from
# passing Haskell tests after the Lean semantics change.
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

cd "$repo_root"

if ! (cd lean && lake build Lara.Examples.Semantics) > "$tmp_dir/lake-build.log" 2>&1; then
  echo "semantics goldens: FAIL: lake build Lara.Examples.Semantics" >&2
  cat "$tmp_dir/lake-build.log" >&2
  exit 1
fi

if ! (cd lean && lake env lean --run SemanticsGoldens.lean) > "$tmp_dir/lean.hs" 2> "$tmp_dir/lean.log"; then
  echo "semantics goldens: FAIL: Lean emitter" >&2
  cat "$tmp_dir/lean.log" >&2
  exit 1
fi

sed -n '/^leanGoldens :: /,/^  ]$/p' test/SemanticsSpec.hs > "$tmp_dir/checked-in.hs"
for output in "$tmp_dir/lean.hs" "$tmp_dir/checked-in.hs"; do
  test -s "$output" || { echo "semantics goldens: FAIL: empty golden block: $output" >&2; exit 1; }
done

if ! diff -u --label lean-emitted.hs --label checked-in.hs "$tmp_dir/lean.hs" "$tmp_dir/checked-in.hs"; then
  echo "semantics goldens: FAIL: test/SemanticsSpec.hs is stale." >&2
  echo "  Replace its leanGoldens block with: cd lean && lake env lean --run SemanticsGoldens.lean" >&2
  exit 1
fi

printf 'semantics goldens: PASS\n'
