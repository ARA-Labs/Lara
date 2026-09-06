# Theory PW-T6: exact checked-support transport

_Status: mechanized on 2026-09-02 (issue #191, tracker #189). This document
records what T6 froze, what it proved, why its obligations clause is exact
rather than conditional, and the limitations its successors T8 (#193) and T9
(#190) inherit._

The intended readers are the paper author, whoever takes decisions on tracker
#189, and whoever implements T8/T9. They should cite the declarations below
rather than re-deriving them; `docs/paper-lean-name-map.md` §PW-T6 carries the
stable keys.

T6 adds a structural layer over the unchanged PW0 wrapper and the unchanged
local checker: three new modules that only import. No local checking,
compilation, grounded labelling, status, or PW0 definition was modified.
The canonical design source is
`lara-paper/plan/possible-world-semantics-brainstorm.md` §Structural Bridge /
§T6; the sizing note it executes is `docs/theory-pw0-outer-model.md` §6.

## 1. What T6 froze

**The translation is a partial symbol map, lifted structurally.**
`PW.SymMap` carries independent partial maps on the predicate and constructor
namespaces (`Lara/PW/Translation.lean`); everything else — variables, numeric
and string literals, rule identifiers, question keys, hole sets, assurances
including the frozen certificate triple — is carried across verbatim, and
evidence leaves are renamed by a separate *total* `LeafId` map. Partiality is
the design's "explicit translation-domain evidence": every lift is
`Option`-valued, `none` exactly at an out-of-vocabulary symbol, and the
transport theorem consumes the `some` hypotheses rather than assuming
totality. The dependent partial support map `T_{b}` of the design is
`PW.trSupport`.

**The contract is three clauses over a shared `canon`** (`PW.StructuralBridge`,
`Lara/PW/Structural.lean`) — one clause per environment parameter the typing
judgment `HasSupport canon Pi Gamma CertOk` reads:

- `leaf_ok`: a leaf typed at `p` in the source is typed at the translated `p`
  in the target under the leaf map ("admitted evidence and artifact
  identity");
- `rule_ok`: the target policy carries, at the *same* rule identifier, exactly
  the translated rule — premises, conclusion, and answers translated; mode,
  parameters, premise order, question keys, the trusted flag, and the
  certifier allowlist preserved on the nose ("sorts, substitutions,
  constructors, identifiers, premise order");
- `cert_ok`: certificate acceptance survives translation of the encoded step
  ("backend registry entries and per-occurrence certificates").

The shared `canon` is a commitment, not an omission: the source canonicalizer
is the one thing two bridged environments must agree on for their conclusions
to be comparable as claims — the same shared binder B0 records for registries
(`docs/theory-b0-backend-compositionality.md`, "two binders ARE shared").

Every contract field is read by a named arm of the transport induction;
issue #191's "every contract field is justified by a proof use or removed"
was applied literally — early drafts carried no field that the final proof
does not consume.

## 2. Theorem table

| Result | Declaration |
|---|---|
| T6 exact checked-support transport | `PW.support_transport` |
| T6 completeness clause | `PW.support_transport_complete` |
| Claim-level transport | `PW.supports_transport` |
| Conclusion law (pattern level) | `PW.instAPat_tr`, `instAPats_tr` |
| `≡` survives translation | `PW.equiv_tr` (via `trAtom_nf`, `trTerm_nf`) |
| Target-side occurrence replay | `PW.transport_occurrences_accounted` |
| Checker-tied applicability | `PW.Admits`, `PW.admits_transport` |
| Identity endobridge | `PW.StructuralBridge.refl`, `Examples.PW.admitsIdT7`, `t7_t6_transport` |
| T6/T8 boundary at a live instance | `Examples.PW.t7_t6_boundary` |
| Renaming instance | `Examples.PW.bridgeRen`, `hasSupport_ren`, `ren_transport` |
| Strict-certificate renaming instance | `Examples.PW.bridgeCert`, `hasSupport_cert`, `cert_transport` |
| Contract clauses exercised off the identity | `Examples.PW.ren_leaf_translated`, `ren_support_renamed`, `cert_accept_translated`, `cert_reject_untranslated`, `cert_support_renamed` |
| Strict-fixture drift guards (#231) | `Examples.PW.cert_reject_mismatched_certifier`, `cert_target_rule`, `cert_only_assurance` |
| Translation-domain negative | `Examples.PW.ren_out_of_vocabulary`, `ren_translationUndefined` |

The renaming instance discharges `rule_ok` and `leaf_ok` under a translation
that actually renames — the target policy carries the translated rule, and the
renamed leaf is admitted at the translated atom. The strict-certificate
instance (#224) discharges the third clause: a strict rule with a live
certifier allowlist and `allowTrusted` off, a `CertOk` pair holding exactly at
the fixture's encoded step on each side, `cert_accept_translated` pinning that
source acceptance at `([e], p)` survives translation to target acceptance at
`([e_r], p_r)`, and `cert_reject_untranslated` pinning that neither side
accepts the other's encoded step. `cert_transport` runs the transported
derivation through
the `AssuranceOk.cert` arm off the identity, the frozen `(β, hd, κ)` triple
carried verbatim. Soundness is carried by `support_transport`, not by these
examples; they are the conformance evidence that all three contract clauses
are inhabitable off the identity.

Because `cert_transport` exercises the strict fixture at exactly one certifier
triple and one encoded step, two mutations of the fixture would leave it green
while making the prose above false. #231 closes both. Dropping `(β, hd, κ)`
from either acceptance judgment — acceptance as a predicate on the encoded
step alone — is rejected by `cert_reject_mismatched_certifier`, which pins
that mismatching exactly one of the three components, with the side's own
encoded step held fixed, is refused on both sides. Flipping
`ruleCert.allowTrusted` on is rejected by `cert_only_assurance`, which pins
the flag off and proves that neither `.trusted` (which needs the flag) nor
`.none` (which needs a defeasible rule) can satisfy `AssuranceOk` at the
fixture's encoded step, in the source *and* in the target environment — so the
certificate arm is the only reachable assurance, which is what makes
`cert_ok` load-bearing. `cert_target_rule` is what ties the target half down:
the target rule is written out independently of `ruleCert` and the equation
`piCertTgt rnCert = some ruleCertTgt` holds by `rfl`, so any drift in
`ruleCert`'s mode, allowlist, or trusted flag breaks it.

`support_transport` states: under the contract, if
`HasSupport canon Pi Gamma CertOk w C O` and `trSupport sym leafMap w = some
w'`, then there is a `C'` with `trAtom sym C = some C'` and
`HasSupport canon Pi' Gamma' CertOk' w' C' O`. The conclusion's translation
definedness is *derived*; the obligation list is the *same* `O`.

## 3. Why obligations transport verbatim

The design phrased completeness conditionally — "transport of a complete
support requires preservation of empty obligations". The mechanization
discharges the condition by proving something stronger: the obligation list
transports *unchanged*, because obligations are lists of question *names*,
question names are rule-local vocabulary the translation never touches
(`trRule_questionNames`, `trRule_mandatoryNames`), and discharge keys and
hole sets are carried verbatim (`trSupportDis_fst`). `collectObligations`
then computes identically on both sides. Completeness (`O = []`) is the
special case, not an extra hypothesis.

The same two commuting facts carry the whole induction:

1. **Instantiation commutes with translation** (`instAPat_tr`): translating a
   substitution and a pattern and then instantiating equals instantiating and
   then translating — variables are untouched, and the instantiated
   constructor name is the pattern's own.
2. **`≡` survives translation** (`equiv_tr`): `nf` canonicalizes numeric
   literals only, the translation renames predicate/constructor names only,
   so the two commute and `nf`-equality is preserved. This is what lets
   premise identity (`premEq`) and discharge answers (`ans`) transport.

## 4. Target-side occurrences replay against the target registry

Instantiating both certificate judgments from registries
(`CertOk := certOkOf reg`, `CertOk' := certOkOf reg'`),
`transport_occurrences_accounted` applies B0's headline
(`hetero_occurrences_accounted`) to the *transported* derivation: every
strict occurrence of the transported term is accounted by its own backend as
registered in the target registry — the target policy carries its rule, the
certificate is accepted by the target instantiation, and the
occurrence-local consequence holds. This is issue #191's replay acceptance
bullet, and it is a corollary rather than a new induction — the intended
signal (as with B0's own accounting laws) that the contract was factored at
the right joint.

## 5. PW0 limitation 1 discharged at structural bridges

PW0 froze `Frame.accept` as an arbitrary `Prop` and recorded that "supplying
that connection is the structural-bridge work of T6"
(`docs/theory-pw0-outer-model.md` §4 limitation 1). The connection supplied
is `PW.Admits`: the target world's accepted program carries the transport of
every argument of the source world's accepted program. `admits_transport`
then turns an admitted edge into checked mathematics: every source argument
transports to a member of the target's own accepted program carrying a
complete checked support for the translated conclusion, checked in the
target context's environment. `Admits` is one checker-tied discipline, not
the only admissible one — `accept` remains a frame parameter, but its name
no longer promises more than any model supplies.

## 6. The T6/T8 boundary, now packaged

`Examples.PW.t7_t6_boundary` states, at the live T7 fixtures: the identity
endobridge's transport succeeds (`Admits` holds between `wT7src` and
`wT7tgt`) *and* `cmpStatus` flips from `justified` to `defeated`. What
`t7_witness` showed before T6 existed — support transport cannot give status
preservation — is now exhibited *through* the T6 machinery itself. T8 (#193)
must therefore quantify over the target's attackers; nothing in this
milestone's theorem set can be strengthened into T8 without new hypotheses.

## 7. Verification (2026-09-06, with the #231 drift guards)

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
separately. No `sorryAx`, no
`ofReduceBool`, no `nativeDecide`, nothing outside `propext` /
`Classical.choice` / `Quot.sound`. The original landing (PR #223, verified
2026-09-02 at 1707 declarations, 78 PW-T6) touched only the three new
modules, the two roots (`Lara.lean`, `AxCheck.lean`), and the two docs — no
existing semantics module (the PW0 gate-1 discipline, carried forward); the
#224 follow-up added the strict-certificate fixtures to
`Lara/Examples/PWStructural.lean` and their six audit rows (verified
2026-09-03 at 1713 declarations, 84 PW-T6), and the #231 follow-up adds the
three drift guards to the same fixture module and their three audit rows.
Neither follow-up touches a semantics module.

Both guards were checked against the mutation each exists to catch, by
mutating the fixture and rebuilding. Making both acceptance judgments ignore
`(β, hd, κ)` fails all six components of
`cert_reject_mismatched_certifier`; setting `ruleCert.allowTrusted := true`
fails `cert_target_rule` and the pinned flag equation inside
`cert_only_assurance`. Both mutations were reverted and the full build and
audit re-run green.

## 8. Known limitations of the frozen contract

These are design commitments, not oversights; each has a named home.

1. **The translation is bridge-global and functional.** One `SymMap` answers
   for every world pair of the bridge; the alias case PW0's feasibility note
   records — one target world resolving a source alias, another not — is
   *not* expressible, and neither is ambiguity (several target queries for
   one source query). The edge-indexed `Translate` relation remains the
   documented fallback (`docs/theory-pw0-outer-model.md` §6), and moving to
   it is a contract change budgeted there, not a refinement here.
2. **The leaf map is total.** A source leaf with no target counterpart cannot
   be expressed; partial evidence translation would push `Option` into the
   leaf arm of `trSupport` and into `leaf_ok`. Defer until a bridge needs it.
3. **Attacks do not transport.** The contract preserves nothing about attack
   structure — deliberately, since basic support checking does not read
   attacks. Attack correspondence is exactly the additional hypothesis T8
   (#193) must introduce. Discharged by T8 (#193): the attack correspondence is
   `PW.StatusBridge` (`forth`/`back`/`matched`); see
   docs/theory-pw-t8-status-preservation.md.
4. **No composition.** Transport along a path of structural bridges, and the
   commuting-triangle conditions for equating a composite with a direct
   bridge, are T9 (#190). `trSupport` composes as a function, but nothing
   here states the bridge-level coherence laws. Discharged by T9 (#190): see
   docs/theory-pw-t9-path-composition.md.
5. **Question keys are frozen across the bridge.** A bridge that renames its
   critical-question vocabulary is not expressible; obligations transport
   verbatim *because* of this. Relaxing it would make "mapped obligations" a
   genuine map and completeness conditional again — do not relax it without
   T8-level need.

Full stable keys: `docs/paper-lean-name-map.md` §PW-T6.
