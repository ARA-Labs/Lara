# The rejection surface: what LARA refuses, what it accepts-but-does-not-support

_Status: reference note, written 2026-08-06. Answers "what does an invalid argument look like, and
how does the checker detect it?" — a question spread across `docs/spec.md` §10, `examples/README.md`,
and the mutant manifest but not previously answered in one place. Every anchor below was re-verified
live against the `lara` binary while writing this note (`cabal build exe:lara`); rerun the commands to
recheck them after a change._

## 1. Two doors, two failure modes

LARA has two entry points, and the same kind of defect surfaces differently depending on which one a
program goes through. This is the least obvious part of the contract and was rediscovered
empirically rather than read off a spec section (`app/Main.hs`, module header, is the authoritative
statement).

- **Source boundary (`.lara`)** — the untrusted elaborator parses the program and its co-located
  policy and builds a checker `Unit`. If it cannot — a parse error, a missing/unreadable policy file,
  or an `ElabError` (duplicate admission key, duplicate leaf id, or a deeper elaboration failure) —
  it refuses to build a unit at all: **exit 2**, nothing on stdout, one located `lara: source
  invalid: …` (or `lara: parse error at …`) line on stderr. The core checker never runs.
- **Core checker (`.sexp`, or a `.lara` that elaborated)** — accepts a `Gamma` and a program and
  decides. A decode failure on a raw `.sexp` (`R14` codec) is also exit 2 with nothing on stdout —
  the checker is the same "cannot even build the input" failure as the elaborator's, just at the
  wire layer instead of the surface-syntax layer. Everything past decoding is **exit 1** plus a
  frozen rejection class printed on stdout as part of the verdict S-expression, e.g.:

  ```
  $ lara check examples/R1/example.lara
  (verdict (replay-id …) reject R1)
  $ echo $?
  1
  ```

So "exit 2" is not exclusively a `.lara`-vs-`.sexp` distinction — it means *decode/elaborate-boundary
failure* on either path (parse error, `ElabError`, or wire codec error). "Exit 1 with a class on
stdout" means the input was well-formed enough to reach the six-stage checker (`Lara.Check`), which
then refused it for a specific, named reason.

There is a third, narrower case worth knowing about: an `R8`-admission-`reject`-classed leaf (a
`certified` leaf without a listed checker witness, or a duplicate table key escalated to `reject`) is
caught by `Lara.Admission` *before* the checker runs, on the `.lara` path. It also exits **1**, but —
unlike a normal checker rejection — prints **no verdict on stdout**, only a located `lara: …` message
on stderr (`app/Main.hs`, the `SourceRejected` branch). It is exit-1-like in code but stdout-silent
like an exit-2 failure; treat "exit 1 with an S-expression verdict on stdout" as the actual signature
of a checker-stage rejection, not the bare exit code.

## 2. The class table, with a runnable anchor per class

`docs/spec.md` §10.1 freezes fourteen rejection classes (R1–R14); the table below adds one runnable
anchor per class, verified against `lara check` at the time of writing. Re-running any command should
reproduce the class shown.

| Class | Trigger | Anchor | Verified output |
| --- | --- | --- | --- |
| R1 reference | leaf/argument/rule/… id named by a support term is not in Γ | `examples/R1` | `lara check examples/R1/example.lara` → `reject R1` |
| R3 substitution | `dom(theta)` misses a rule parameter | `fixtures/mutants/A--wrong-subst-domain-0.sexp` | `reject R3` |
| R4 premise | cited term's conclusion `≢` the rule's instantiated premise pattern | `fixtures/mutants/A--wrong-premise-0.sexp` | `reject R4` |
| R5 question-accounting | a declared question is in neither the discharge map nor the hole set (or vice versa) | `fixtures/mutants/A--open-obligation-0.sexp` | `reject R5` |
| R6 discharge | discharging term's conclusion `≢` the instantiated answer pattern | `fixtures/mutants/A--wrong-discharge-0.sexp` | `reject R6` |
| R7 assurance | `trusted` without `allow-trusted`; `cert` with no matching certifier entry; assurance on a defeasible rule; a strict rule carrying a discharge map or holes | `fixtures/mutants/A--trusted-assurance-0.sexp` | `reject R7` |
| R9 data-integrity | duplicate-report group with `≢` members, escalated to `reject` by policy | `fixtures/corpus/reject-r9.sexp` | `reject R9` |
| R10 attack-position | attack position undefined, or wrong occurrence kind for the attack kind | `examples/R3` | `lara check examples/R3/example.lara` → `reject R10` |
| R11 attack-relation | no declared contrary pair licenses the rebut/undermine; no declared exception licenses the undercut | `fixtures/mutants/A--unlicensed-attack-0.sexp` | `reject R11` |
| R12 policy-wf | a `contrary` side may overlap a strict-reachable pattern (spec §8.1 Path B) | `examples/R2` (spec class R12, despite the directory name — see its header comment) | `lara check examples/R2/example.lara` → `reject R12` |
| R13 backend | certificate replay rejects; unknown backend/version; theory digest not allowlisted | `fixtures/corpus/ord-lt-boundary-reject.sexp` | `reject R13`, stderr: `certificate replay: ord@1 (theory t0) rejected the certificate: the claimed comparison does not hold: 5 < 5 is false` |
| R14 codec | wire program fails to decode: malformed JSON/S-expression, unknown fields, presentation parse error | `fixtures/mutants/malformed/A--codec-core-version-0.sexp` | exit 2, stderr: `lara: codec error at replay-id: unsupported core version: "lara-core@0.2"`, **nothing on stdout** |

Two classes are not individually anchored above because they are exercised only inside larger
worked cases rather than by one dedicated file:

- **R2 signature** (arity/symbol mismatch against `Sigma`, or a non-ground term where ground is
  required) — the spec's own class R2, not to be confused with the `examples/R2` directory, which
  demonstrates R12 (see its header comment and the m4a-checklist §3 note on the naming collision).
- **R8 admission** (a `reject`-classed leaf, or a `certified` leaf missing its checker witness) — see
  §1's third case above; it is a source-boundary rejection distinct from both the R1–R14 checker
  classes above it in the table and from quarantine below it.

The full mutation manifest (`fixtures/mutants/MANIFEST.tsv`, 369 mutants) exercises every class at
scale and is the authoritative cross-check if an anchor above ever drifts; each row names its
`expected` outcome (`reject-R1`, …, `codec-reject`) and `expected-location`.

Two constructs are **deliberately not rejection classes**, per spec §10.1:

- **Quarantine** (§4.3) — the source boundary prunes a quarantined leaf, every dependent argument,
  and any attack with a removed raw endpoint, *before* core checking. The pruned unit can still be
  accepted (typically with a weaker status); nothing is refused.
- **Attack cycles** — these evaluate to `undec`/`contested` under the grounded semantics (§8), not to
  a rejection.

## 3. The line that actually matters: invalid vs. unsupported

The natural reading of a paper's *evidence* not supporting its *claim* is "the checker should reject
it." That is wrong, and it is the headline of this document.

- **invalid** — malformed, or a certificate that does not replay: an `R1`–`R14` rejection (§2).
- **valid but unsupported** — accepted, with status `gap` / `defeated` / `contested`.

```
$ lara check examples/E2/example.lara
(verdict (replay-id …) accept (labels) (edges)
  (statuses (status (atom improves (con M) (con accuracy) (con D)) gap)))
$ echo $?
0
```

`examples/E2` declares every leaf its evidence needs but never assembles an argument that concludes
the headline claim. It compiles cleanly and exits **0** with status `gap` — the argument was never
built, which is different from `examples/R1`'s argument that cites a leaf which does not exist
(`reject R1`, exit 1). An undeclared reference and an unbuilt argument are different failures; the
calculus keeps them apart (see `examples/R1/example.lara`'s own closing "teaching point" comment,
which states this contrast directly).

Most *scientific* problems — weak evidence, an unaddressed critical question, a contested field —
land in the "valid but unsupported" bucket by design
(`docs/comparison-rit-lara.md` §6.2: "a rejected extractor should not automatically become a
counter-argument"). The natural assumption is the opposite of how the calculus is built, so this is
worth stating plainly rather than leaving a reader to infer it.

The seeded mutation suite quantifies the split. Of 369 mutants, 311 reject across the R1–R14/codec
classes and 58 are *accept* mutants; of those, 49 have a ground-truth **status change**
(`accept-defeated` 18, `accept-contested` 9, `accept-gap` 9, `accept-evidence-blocked` 9,
`accept-all-contested` 4) and the remaining 9 (`accept-justified`) exercise mutations the checker
correctly absorbs without a status change. Both halves are byte-identical across the Haskell and Lean
drivers (`scripts/differential.sh`).

## 4. Relationship to `rit` (the question that prompted this)

- **Genuine overlap.** `rit`'s refusal rule — "if a value cannot be re-derived, refuse rather than
  guess" — corresponds to LARA's R13: a certificate whose cited cells do not support the claimed
  ordering. Since #84, R13's `ord@1` rejection explains itself on stderr, e.g. (live output from
  `fixtures/corpus/ord-lt-boundary-reject.sexp`):

  ```
  certificate replay: ord@1 (theory t0) rejected the certificate:
    the claimed comparison does not hold: 5 < 5 is false
  ```

  The premise-only guard (also #84, `fixtures/corpus/ord-premise-only-reject.sexp`) is the second
  half of the same idea: an artifact cannot self-supply a compared value as a theory entry instead of
  citing measured evidence (`ord cites premise slots only; slot names theory entry 0`).

- **No overlap, and this must not be overclaimed.** `rit`'s running example — two authors reporting
  contradictory `modded-nanogpt` speedrun numbers — compiles fine in LARA on *both* sides: each
  author's arithmetic is impeccable. It resolves as `contested`, and once an unrecorded batch-size
  dimension enters the setting index, the contrary pattern stops unifying and both claims stand
  `justified` (the `examples/agreement-map` P2 mechanism). Writing "LARA rejects these too" would
  contradict LARA's own spec — the contradiction is a defeat-calculus outcome (`contested`), not an
  R-class rejection.

## 5. One counterintuitive finding worth recording

Renaming a leaf id does **not** produce R1 in the surface language.

`.lara` rule premises resolve by *matching the leaf's proposition* against the instantiated premise
pattern, not by citing leaf ids directly — so a renamed leaf whose proposition is unchanged still
resolves, and the unit accepts. Producing R1 needs a support term that names a missing id explicitly
(`by leaf(e_missing)` as in `examples/R1`, or a discharge referencing a missing id). This is easy to
get backwards while constructing negative examples: the intuitive way to build an R1 case — rename a
leaf and leave a stale reference — does not work, because the surface elaborator is matching on
content, not on the name.

(At the core wire layer this looks different: the `leaf l` support-term rule *does* look `l` up in
`Gamma` by id, per spec §6.1, and a raw core caller that submits a `leaf l` term with no matching `Γ`
entry gets R1 directly. The surprise is specific to the `.lara` presentation boundary's premise
resolution, not the core judgment.)

## Out of scope

**Byte-level evidence admission** (issue #78, gated design — `docs/evidence-admission-decision.md`).
A leaf is *declared* evidence, checked for admission (kind × provenance) and, for `certified` leaves,
for a checker witness — it is not byte-checked against the underlying artifact. No rejection class in
§2 covers "the number is not actually in the artifact"; that guarantee does not exist yet, and this
document should not be read as implying it does.

## See also

- `docs/spec.md` §10.1 — the frozen class table this document adds anchors and prose to.
- `examples/README.md` — the worked-example suite (`A`, `B`, `E1`–`E5`, `R1`–`R3`, `S1`–`S4`), several
  of which are the anchors above.
- `fixtures/mutants/README.md` and `MANIFEST.tsv` — the generated mutation suite that exercises every
  class at scale, differentially checked between the Haskell and Lean drivers.
- `docs/comparison-rit-lara.md` §6.2 — the invalid/unsupported distinction as it bears on the `rit`
  comparison.
