# PW-T6 — exact checked-support transport

## Result

Branch `theory/191-pw-t6-structural-transport` (commit 13ae1d7) established the
transport; the follow-up branch `theory/224-cert-ok-witness` (witness commit
48187b0) added the strict-certificate witness. Three new modules that only
import — `Lara.PW.Translation`, `Lara.PW.Structural`,
`Lara.Examples.PWStructural` — over the unchanged local checker and the
unchanged PW0 wrapper.

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

All three contract clauses are discharged non-vacuously off the identity:
`rule_ok` by the translated policy, `leaf_ok` by the renamed leaf admitted at
the translated atom (`ren_leaf_translated`, with `ren_support_renamed`
pinning that the transported term is not the source term), and — closing
the strict-certificate follow-up — `cert_ok` by the strict-certificate renaming bridge (`bridgeCert`):
a strict rule with a live certifier allowlist and `allowTrusted` off, a
`CertOk` pair holding exactly at the fixture's encoded step on each side,
`cert_accept_translated` pinning that source acceptance at `([e], p)`
survives translation to target acceptance at `([e_r], p_r)`,
`cert_reject_untranslated` pinning that neither side accepts the other's
encoded step, and `cert_transport` running the transported derivation through
the `AssuranceOk.cert` arm with the frozen `(β, hd, κ)` triple carried verbatim
(`cert_support_renamed`). Soundness is carried by `support_transport`; the
examples are the conformance evidence that the frozen contract is
inhabitable off the identity.

Two mutations of the strict fixture would leave `cert_transport` green while
making its prose false; the drift-guard follow-up closes both.
`cert_reject_mismatched_certifier` pins that each of the three frozen
components is load-bearing on each side — with the side's own encoded step
held fixed, mismatching exactly one of `β`, `hd`, `κ` is refused — so
certifier-blind acceptance breaks a named audited theorem.
`cert_only_assurance` pins `allowTrusted` off and proves that neither
`.trusted` (which needs the flag) nor `.none` (which needs a defeasible rule)
can satisfy `AssuranceOk` at the fixture's encoded step, source and target,
so the certificate arm is the only reachable assurance;
`cert_target_rule` ties the target half down by stating the translated rule
independently of `ruleCert` and holding by `rfl`.

## Verification (2026-09-06, with the drift guards)

```
$ cd lean && lake build
Build completed successfully (148 jobs).                        EXIT: 0

$ cd lean && (set -o pipefail; lake env lean AxCheck.lean | ../scripts/check-axioms.sh)
Axiom audit passed.                                             EXIT: 0
```

2495 audited declarations across the library, of which 87 are PW-T6 — every
theorem the three modules declare, together with the translation and bridge
definitions those theorems are stated over. The two structures (`SymMap`,
`StructuralBridge`) and the renaming-example fixtures are audited
transitively, through the gated theorems that mention them: `#print axioms`
reports the whole dependency set, and the repo-wide convention is that
example fixtures are gated through their theorems rather than registered
separately. No `sorryAx`, no `ofReduceBool`, no `nativeDecide`, nothing
outside `propext` / `Classical.choice` / `Quot.sound`.
The original landing's `git diff main` (verified 2026-09-02 at 1707
declarations, 78 PW-T6) was pure insertion, 2142 lines over 7 files, the only
Lean files touched outside the three new modules being the two roots
`Lara.lean` and `AxCheck.lean`; the cert-witness
follow-up added the
strict-certificate fixtures to `Lara/Examples/PWStructural.lean` and their
six audit rows (verified 2026-09-03 at 1713 declarations, 84 PW-T6); the
drift-guard
follow-up adds three drift guards to the same fixture module and their three
audit rows. Neither follow-up touches a semantics module.

Each guard was checked against the mutation it exists to catch, by mutating
the fixture and rebuilding: making both acceptance judgments ignore
`(β, hd, κ)` fails all six components of
`cert_reject_mismatched_certifier`; setting `ruleCert.allowTrusted := true`
fails `cert_target_rule` and the pinned flag equation inside
`cert_only_assurance`. Both mutations were reverted and the full build and
audit re-run green.

## Boundary

The theorem neither assumes nor concludes grounded status preservation: no
attack structure appears in the contract, and `t7_t6_boundary` exhibits the
gap at the live T7 fixtures through the T6 machinery itself. Status
preservation must quantify over the target's attackers — T8; exact
structural-path composition is T9.

Frozen limitations (each with a named home): bridge-global functional
translation (edge-indexed `Translate` relation remains the documented
fallback, a contract change budgeted in `docs/theory-pw0-outer-model.md` §6);
total leaf map; no attack transport (T8); no composition laws (T9); question
keys frozen across the bridge (what makes obligations transport verbatim).

Full record: `docs/theory-pw-t6-structural-transport.md`.
