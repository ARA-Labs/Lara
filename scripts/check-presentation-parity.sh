#!/usr/bin/env bash
set -euo pipefail

# Cross-language presentation-shape parity gate (guard pipeline — see plan D4):
#
#  Haskell types ──cabal build──▶ presentation-shape.hs ──┐  witnesses: compile-time
#   (Lara.AST,                    (witnesses + shape      │  tripwire: rows ==
#    Lara.Sigma)                   tripwire + shapeRows)  ▼            real shape
#                                                  haskell.tsv ──┐
#                                                                ├─ diff -u ─▶ PASS/FAIL
#                                                    lean.tsv ───┘
#   Lean types  ──lake build───▶ presentation-shape ──────▲
#    (Lara.Presentation)          (lean_exe: witnesses + shapeRows)
#
# SortName is witnessed but row-erased (Lean's Sigma carries List String).
# Cert's payload is each language's native S-expression type and is exempt from
# shape comparison. Both witness files state the two exemptions in full.
#
# Both runtimes are rebuilt here, so a stale artifact can never produce a false
# PASS. The guard never parses source text: exact constructor signatures pin
# record fields, sum payloads, aliases, and anonymous entry types. Shape
# tripwires re-derive row counts and named selector order from each language's
# real declarations before either inventory is compared.

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

cd "$repo_root"

if ! cabal build lib:lara > "$tmp_dir/cabal-build.log" 2>&1; then
  echo "presentation parity: FAIL: cabal build lib:lara" >&2
  cat "$tmp_dir/cabal-build.log" >&2
  exit 1
fi
if ! (cd lean && lake build presentation-shape) > "$tmp_dir/lake-build.log" 2>&1; then
  echo "presentation parity: FAIL: lake build presentation-shape" >&2
  cat "$tmp_dir/lake-build.log" >&2
  exit 1
fi

lean_bin="lean/.lake/build/bin/presentation-shape"
[ -x "$lean_bin" ] || { echo "presentation parity: FAIL: no Lean binary at $lean_bin" >&2; exit 1; }

cabal exec -- runghc scripts/presentation-shape.hs > "$tmp_dir/haskell.tsv"
"$lean_bin" > "$tmp_dir/lean.tsv"

for output in "$tmp_dir/haskell.tsv" "$tmp_dir/lean.tsv"; do
  test -s "$output" || { echo "presentation parity: FAIL: empty inventory: $output" >&2; exit 1; }
done

# Stable labels so the diff reads the same locally and in CI (the temp paths do
# not), plus the fix rule: an inventory row is only ever correct in duplicate.
if ! diff -u --label haskell.tsv --label lean.tsv "$tmp_dir/haskell.tsv" "$tmp_dir/lean.tsv"; then
  { echo "presentation parity: FAIL: inventories differ."
    echo "  A presentation type changed on one side only. Update BOTH inventories in one change:"
    echo "    scripts/presentation-shape.hs        (shapeRows + shapeChecks)"
    echo "    lean/Lara/PresentationParity.lean    (shapeRows + shapeChecks)"; } >&2
  exit 1
fi
printf 'presentation parity: PASS (%s rows)\n' "$(wc -l < "$tmp_dir/haskell.tsv" | tr -d ' ')"
