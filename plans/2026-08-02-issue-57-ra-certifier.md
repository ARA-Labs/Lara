# Issue #57 — exercise the strict/certificate path: `ra@1` rational-arithmetic certifier

> **Status: complete — closed by PR #59 (2026-08-03).**

Goal: make the paper's claim-support number (4) — fraction of load-bearing
strict steps carrying a checked certificate — a real, non-zero measurement.
Target unit: `corpus-units/adaptive-pruning/C04` (annotation
`strict_certifier: domain-checker(rational-arithmetic)`), the smallest honest
certifier: re-check that (50.0 − 38.1) / 50.0 = 0.238 and that 0.238 exceeds
the 5%-relative falsification threshold, in exact rational arithmetic.

## What already exists (no new seam needed)

- The backend seam is fully general: `Lara.Strict.Backend` (Haskell) /
  `Lara.Strict.Backend canon` (Lean, `lean/Lara/Strict.lean:77`) with the
  LCF-sealed `strictCheck`, closed registry, dependency accountability.
- The wire carries `Cert{backend, version, theory, payload}` and the
  `theories` section generically; the surface certificate syntax
  (`assurance = cert(nd@1, sha256:…, payload)`) and `certifiers` rule field
  are exercised end-to-end by worked example S1.
- `Prop.Term` has first-class numeric literals (`TNum`, normalized by
  `canonNum`) — the score cells 50.0 / 38.1 / thresholds are representable
  with no grammar change.
- The #56 aggregator (`Lara.ClaimSupport.computeUnit`) already computes (4)
  from real rule modes: an `in`-labelled arg whose root rule is `Strict` is a
  denominator entry; `AssuranceCert` on that root is a numerator entry. It
  goes non-zero automatically once the corpus contains one such arg.

The only missing pieces are (i) one concrete registered backend and (ii) one
corpus unit instantiating it — plus the re-freeze this forces.

## Work breakdown

### W1 — Haskell backend `Lara.Strict.RA` (`ra@1`)
New module mirroring `Lara.Strict.ND`'s shape (414 lines; RA should be much
smaller). Scope of the checker, deliberately minimal:
- Form: exact rationals parsed from `TNum` surface strings (decimal → ℚ);
  goal shape: a closed relative-drop (in)equality, e.g.
  `rel_drop_ge(full, ablated, claimed, threshold)`.
- Replay: recompute `(full − ablated) / full` in ℚ, check it equals `claimed`
  (exact) and `claimed ≥ threshold`. Total, deterministic, no floats.
- Payload: carries the claimed value as an exact fraction (or is a bare
  marker — decision D1 below); decode failures are `BackendRejected`.
- Theory: empty (digest-addressed, like S1's `strict-v1-theory-0`).
- Dependencies: the premise slots actually consulted (obligation 4).

### W2 — registry generalization (both drivers, byte-identical)
- `Lara.Driver.buildCertOk` (src/Lara/Driver.hs:249) hardcodes `nd@1`;
  generalize to a fixed two-entry registry [nd@1, ra@1].
- Lean `Lara.Driver.buildRegistry` (lean/Lara/Driver.lean:658) likewise.
- Verify the surface parser accepts `ra@1` in `use backends […]` and in
  `cert(…)`/`certifiers` (expected generic `name@version`; confirm).

### W3 — Lean metatheory (mechanization discipline, CLAUDE.md)
Instantiate `Backend canon` for RA in a new `lean/Lara/RA.lean` (or extend
`Certificate.lean`), discharging the structure obligations:
`enc_iff`, `replayFull_iff`, `soundFull` (correctness of the exact ℚ
evaluator — `modelsFull` is the mathematical inequality over the parsed
rationals), `uses_covers` + validity. Much smaller than ND.lean's 868 lines:
no proof terms, just decidable arithmetic. `sorry`-free, standard axiom trio,
`AxCheck.lean` extended.

### W4 — policy: strict rule in `corpus-v1`
Add to `corpus-units/corpus-v1.policy.lara` a strict rule (e.g.
`rational_drop_recheck(...)`) with `certifiers = [ (ra@1, sha256:…) ]` and
the empty theory. NOTE: every `unit.core.sexp` embeds the full policy, so
this ripples through all 60 units (see W6).

### W5 — re-lower `adaptive-pruning/C04`
- Add the two score-cell leaves (50.0, 38.1 from E03/Table 5) and a
  sub-claim for the derived arithmetic fact; support it with one arg rooted
  at the strict rule, `assurance = cert(ra@1, sha256:…, payload)`.
- `use backends [nd@1, ra@1]` → the unit's replayId tuple changes.
- The headline claim c04 stays `gap` (variance CQ still unmet — no change to
  the honest status story); do NOT add a second `status` query, so number
  (1) remains a 60-claim distribution. Number (4) becomes 1/1 with the
  documented strict-flavored population (context) unchanged.

### W6 — re-freeze
Policy bytes changed ⇒ all 60 `unit.core.sexp` regenerate ⇒ mutant suite
regenerates (seeded, reproducible) ⇒ differential (`scripts/differential.sh`)
and `scripts/measure.hs` + `scripts/claim-support.hs` re-run ⇒ new hashes in
`docs/m5-freeze-checklist.md` ⇒ tag `m5-freeze-v2`.
Precondition: create the still-missing `m5-freeze-v1` tag on current main
first, so the #56-reported (4)=0 state stays addressable.

## Decisions to settle before implementing

- D1 payload shape: bare marker (replay recomputes everything) vs. payload
  carrying the claimed fraction. Recommend the fraction: the certificate then
  *is* the claimed number, and a corrupted payload is rejectable — better
  mutation surface and a more honest "checked certificate".
- D2 goal/premise split: which cells are premise slots (leaf-fed) vs. baked
  into the goal. Recommend: score cells as premise conclusions from the two
  leaves (dependency accountability then names them), threshold in the goal.
- D3 whether to add a cert-corruption mutation operator over the new strict
  arg in the same PR or as a follow-up suite extension. Recommend follow-up
  (keeps this PR reviewable; T1 already covers codec corruption classes).

## Order

W1 → W2 (Haskell green, S1 + new unit fixture through both front doors) →
W3 (Lean instance + AxCheck) → W4/W5 (policy + unit, differential green) →
W6 (regenerate, re-measure, checklist, tags v1 then v2).
