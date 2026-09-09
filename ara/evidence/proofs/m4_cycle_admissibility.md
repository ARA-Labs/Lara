# Admissible three-cycle (#270)

The generic congruence witness now uses the cycle where grounded and stable
observations differ. This closes C49's disagreeing-carrier fixture boundary,
without changing the general theorem or proving certificate replacement.

In `lean/Lara/Examples/ContextSemantics.lean`:

- `cycle_sideOk_ctx`: the singleton context has no internal contrary pair.
- `cycle_sideOk_frag`: support uniqueness fixes each leaf's conclusion; the
  four internal argument pairs leave only `s ⊣ p`, covered by the declared
  undermine attack at the target's root.
- `cycle_admissible`: both side proofs and the remaining finite checks establish
  admissibility for every registry.
- `congruence_witness_sem`: instantiates `backend_replacement_congruence_sem`
  at that admissible cycle. `obsSem_cycle_stable_ne_grounded` still pins
  grounded's contested result, stable's no-extension result, and their inequality.

The fragment contains only leaves, so certificate relabeling is the identity.
The certificate-bearing instance remains #269. The registry-swap witness
remains on the old chain where all five semantics agree.

Verification performed with Lean 4.32.0:

- Direct kernel check of `ContextSemantics.lean`: exit 0, no warnings.
- Full `lake build`: `Build completed successfully (158 jobs).` Existing
  warnings remain in unrelated modules.
- Full `AxCheck.lean` audit: `Axiom audit passed.`
- Whole-tree declaration coverage: `AxCheck coverage passed (2622 declarations).`
- Axiom and coverage gate self-tests: passed.

The new admissibility obligation was checked before its implementation and
failed on the absent proof. After implementation, the kernel accepted it.
Independent review found stale documentation boundaries, which were corrected.
