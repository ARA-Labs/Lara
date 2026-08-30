#!/usr/bin/env bash
set -euo pipefail

# Cross-language `certDeps` conformance for the heterogeneous term (B0).
#
# Rebuilds the Lean witness, runs lean/BackendDepsGolden.lean, and diffs its
# canonical encoding against the committed test/backend-deps.golden. The
# Haskell side of the same file is asserted by test/StrictSpec.hs'
# `prop_mixedBackendDepsGolden`, which reads the identical bytes and compares
# them with its own encoding of `Lara.Strict.Deps.certDeps` on
# `test/StrictSpec.hs`' `mixedTerm`. Neither side can drift alone: this gate
# fails if Lean moves, the Haskell test fails if Haskell moves, and the golden
# is the single artifact both are pinned to.
#
# WHY THIS GATE IS THE STRONGEST CROSS-LANGUAGE EVIDENCE IN B0
#
# Everything else in lean/Lara/Examples/BackendComposition.lean that needs a
# *typed* heterogeneous term runs its child on the `fixCore` fixture, because
# real `ord@1` *acceptance* is kernel-opaque under Lean 4.32's Slice-based
# String API (`String.splitOn` / `String.startsWith` do not reduce). This gate
# is untouched by that split: `Lara.Support.stepDeps` never calls
# `acceptsFull`. It needs the rule, `instAPats`, the registry entry and
# `resolveTheory` to resolve, then maps each backend's own `uses` over the
# reported slots — and `ord@1`'s `uses` reaches `String.toNat?`, which *is*
# provable per literal (the `Lara.ND.decodeNat_leading_zero_01` treatment).
#
# So both halves of this golden are computed by the REAL SHIPPED backend cores,
# `Lara.Strict.ndBackend` and `Lara.Ord.ordBackend` — the same two
# `Lara.Driver.buildRegistry` registers. No fixture core appears anywhere in
# it. The acceptance split does NOT weaken this artifact.
#
# The Lean witness additionally proves, in the kernel, that *both* backends
# contribute a non-empty report
# (`depsMixedTerm_both_halves_nonempty`) — a golden where one identity
# contributed nothing would pass byte-for-byte while proving nothing about
# heterogeneity.
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT HUP INT TERM

cd "$repo_root"

golden="test/backend-deps.golden"

if ! (cd lean && lake build Lara.Examples.BackendComposition) > "$tmp_dir/lake-build.log" 2>&1; then
  echo "backend deps golden: FAIL: lake build Lara.Examples.BackendComposition" >&2
  cat "$tmp_dir/lake-build.log" >&2
  exit 1
fi

if ! (cd lean && lake env lean --run BackendDepsGolden.lean) > "$tmp_dir/lean.golden" 2> "$tmp_dir/lean.log"; then
  echo "backend deps golden: FAIL: Lean emitter" >&2
  cat "$tmp_dir/lean.log" >&2
  exit 1
fi

test -s "$tmp_dir/lean.golden" || {
  echo "backend deps golden: FAIL: the Lean emitter produced no output." >&2
  exit 1
}

test -s "$golden" || {
  echo "backend deps golden: FAIL: $golden is missing or empty." >&2
  exit 1
}

if ! diff -u --label lean-emitted --label "$golden" "$tmp_dir/lean.golden" "$golden"; then
  echo "backend deps golden: FAIL: $golden is stale." >&2
  echo "  Regenerate with: (cd lean && lake env lean --run BackendDepsGolden.lean) > $golden" >&2
  echo "  Then re-run the Haskell suite — test/StrictSpec.hs asserts the same bytes." >&2
  exit 1
fi

printf 'backend deps golden: PASS\n'
