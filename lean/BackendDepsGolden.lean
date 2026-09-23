import Lara.Examples.BackendComposition

open Lara.Examples.BackendComposition

/-- Emit the canonical `certDeps` encoding of the **shipped** heterogeneous
vectors — `Lara.Examples.BackendComposition.depsMixedTerm` and `depsDupTerm`,
each an `nd@1` root over `ord@1` premises, both computed by the cores
`Lara.Driver.buildRegistry` registers.  `scripts/check-backend-deps-golden.sh`
diffs this against `test/backend-deps.golden`, which `test/StrictSpec.hs`
independently asserts from the Haskell `Lara.Strict.Deps.certDeps`.

Read the word *shipped* literally.  Everything else in
`Lara/Examples/BackendComposition.lean` that needs a **typed** heterogeneous
term runs its child on the `fixCore` fixture, because `ord@1` *acceptance* is
kernel-opaque under Lean 4.32's Slice-based `String` API.  This emitter is not
affected by that: `Lara.Support.stepDeps` never calls `acceptsFull`.  It needs
only the rule, `instAPats`, the registry entry and `resolveTheory` to resolve,
and then maps each backend's own `uses` over the reported slots — and `ord@1`'s
`uses` reaches `String.toNat?`, which *is* provable per literal, rather than
`String.splitOn`/`startsWith`, which are not.  So this golden is the one place
in B0 where both languages compute the same thing over the same two shipped
backends, and the acceptance split does not weaken it.

Not part of the library surface; it exists to be run by the gate:

    cd lean && lake env lean --run BackendDepsGolden.lean
-/
def main : IO Unit :=
  IO.println backendDepsGolden
