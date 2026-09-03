# PW-T6 — exact checked-support transport

## Result

Issue #191, tracker #189, PR #223 (branch `theory/191-pw-t6-structural-transport`,
commit 13ae1d7). Three new modules that only import — `Lara.PW.Translation`,
`Lara.PW.Structural`, `Lara.Examples.PWStructural` — over the unchanged local
checker and the unchanged PW0 wrapper.

The `StructuralBridge` contract is exactly three clauses over a shared source
canonicalizer, one per environment parameter the typing judgment
`HasSupport canon Pi Gamma CertOk` reads: `leaf_ok` (admitted evidence
translates under the leaf map), `rule_ok` (the target policy carries the
translated rule at the same identifier), `cert_ok` (certificate acceptance
survives translation of the encoded step). The main theorem:

```
support_transport :
    HasSupport canon Pi Gamma CertOk w C O →
    trSupport B.sym B.leafMap w = some w' →
    ∃ C', trAtom B.sym C = some C' ∧
      HasSupport canon Pi' Gamma' CertOk' w' C' O
```

The obligation list `O` transports **verbatim** — question keys are rule-local
names the translation preserves (`trRule_questionNames`,
`trSupportDis_fst`) — so the design's conditional completeness clause is the
`O = []` special case (`support_transport_complete`), not an extra hypothesis.

Two commuting facts carry the whole induction: `instAPat_tr` (instantiation
commutes with translation; variables untouched, instantiated constructor name
is the pattern's own) and `equiv_tr` (`≡` survives translation, because `nf`
canonicalizes numeric literals only while the translation renames
predicate/constructor names only).

Corollaries, each without a new induction: `supports_transport` (claim level,
`≡`-closure survives), `transport_occurrences_accounted` (B0's
`hetero_occurrences_accounted` applied to the transported derivation — target
strict occurrences replay against the target registry), and
`admits_transport` (the checker-tied applicability judgment `Admits`
discharging PW0 limitation 1 at structural bridges).

Examples: the identity endobridge (`StructuralBridge.refl`) at the T7 pair
with the packaged boundary `t7_t6_boundary` — transport succeeds and
`cmpStatus` still flips `justified → defeated` — and a genuine
predicate-renaming bridge `p ↦ p_r`, `e ↦ e_r` (`bridgeRen`,
`ren_transport`) whose target policy is the translated policy and whose
evidence typing carries a renamed leaf, plus the domain negative
(`ren_out_of_vocabulary`, `ren_translationUndefined`).

Two of the contract's three clauses are discharged non-vacuously by the
renaming bridge: `rule_ok` by the translated policy, and `leaf_ok` by the
renamed leaf admitted at the translated atom (`ren_leaf_translated`, with
`ren_support_renamed` pinning that the transported term is not the source
term). `cert_ok` has no off-identity witness — it needs a strict rule with a
live certifier allowlist and a certificate-accepting environment on both
sides, deferred to #224. This is a gap in conformance evidence, not in
soundness: `support_transport` carries the theorem.

## Verification (2026-09-02)

```
$ cd lean && lake build
Build completed successfully (130 jobs).                        EXIT: 0

$ cd lean && (set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
Axiom audit passed.                                             EXIT: 0
```

1707 audited declarations across the library, of which 78 are PW-T6 — every
theorem the three modules declare, together with the translation and bridge
definitions those theorems are stated over. The two structures (`SymMap`,
`StructuralBridge`) and the renaming-example fixtures are audited
transitively, through the gated theorems that mention them: `#print axioms`
reports the whole dependency set, and the repo-wide convention is that
example fixtures are gated through their theorems rather than registered
separately. No `sorryAx`, no
`ofReduceBool`, nothing outside `propext` / `Classical.choice` / `Quot.sound`.
`git diff main` is pure insertion, 2142 lines over 7 files; the only Lean
files touched outside the three new modules are the two roots `Lara.lean` and
`AxCheck.lean`.

## Boundary

The theorem neither assumes nor concludes grounded status preservation: no
attack structure appears in the contract, and `t7_t6_boundary` exhibits the
gap at the live T7 fixtures through the T6 machinery itself. Status
preservation must quantify over the target's attackers — T8 (#193); exact
structural-path composition is T9 (#190).

Frozen limitations (each with a named home): bridge-global functional
translation (edge-indexed `Translate` relation remains the documented
fallback, a contract change budgeted in `docs/theory-pw0-outer-model.md` §6);
total leaf map; no attack transport (T8); no composition laws (T9); question
keys frozen across the bridge (what makes obligations transport verbatim).

Full record: `docs/theory-pw-t6-structural-transport.md`. Stable citation
keys: `docs/paper-lean-name-map.md` §PW-T6.
