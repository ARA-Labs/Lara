#!/usr/bin/env bash
set -euo pipefail

# Exhaustive Haskell/Lean parity for the four Lara.Update constructor-side
# deciders. Both runtimes generate the same canonical TSV from their native
# source carriers; Lean is the semantic oracle.
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

cd "$repo_root"

if ! cabal build lib:lara > "$tmp_dir/cabal-build.log" 2>&1; then
  echo "update differential: FAIL: cabal build lib:lara" >&2
  cat "$tmp_dir/cabal-build.log" >&2
  exit 1
fi
if ! (cd lean && lake build update-preconditions) > "$tmp_dir/lake-build.log" 2>&1; then
  echo "update differential: FAIL: lake build update-preconditions" >&2
  cat "$tmp_dir/lake-build.log" >&2
  exit 1
fi

lean_bin="lean/.lake/build/bin/update-preconditions"
if [[ ! -x "$lean_bin" ]]; then
  echo "update differential: FAIL: no Lean binary at $lean_bin" >&2
  exit 1
fi

if ! cabal exec -- runghc scripts/update-preconditions.hs > "$tmp_dir/haskell.tsv"; then
  echo "update differential: FAIL: Haskell emitter" >&2
  exit 1
fi
if ! "$lean_bin" > "$tmp_dir/lean.tsv"; then
  echo "update differential: FAIL: Lean emitter" >&2
  exit 1
fi

for output in "$tmp_dir/haskell.tsv" "$tmp_dir/lean.tsv"; do
  if [[ ! -s "$output" ]]; then
    echo "update differential: FAIL: empty inventory: $output" >&2
    exit 1
  fi
done

if ! diff -u --label haskell.tsv --label lean.tsv \
    "$tmp_dir/haskell.tsv" "$tmp_dir/lean.tsv"; then
  echo "update differential: FAIL: Lara.Update precondition decisions differ" >&2
  exit 1
fi

printf 'update differential: PASS (%s decisions)\n' \
  "$(wc -l < "$tmp_dir/haskell.tsv" | tr -d ' ')"
