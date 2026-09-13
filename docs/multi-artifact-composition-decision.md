# Decision: composing independently checkable artifacts into a map

_Status: the composition boundary is settled, and every stage behind it has
landed. Recorded 2026-09-10 for issue #303, with the first increment
(`Lara.Map.Types`, `Lara.Map.Wire`, `test/MapWireSpec.hs`), which shipped the
vocabulary, the two grammars, and their codecs only. Loading, qualification,
linking, the `.laramap` driver, `--out`, and the worked example landed behind
this record, each amending it as it went; nothing may change them without
amending this file again. **No corpus regeneration and no freeze-tag bump is owed:** the
layer is strictly additive above `lara-core@0.2`, and no corpus unit, mutant, wire,
replay-identity, or golden byte changes — the only core-side edit is two additive exports of an
existing `Lara.Wire` production. Companion to `docs/spec.md` §12 and its dated
#303 amendment (the versioned extension marker), `strict-backend-decision.md` (the shared-contract
fields a member is compared on), and `rejection-surface.md` (the two-exit-code
door story a map inherits)._

## What a map is

A **map** is a set of independently authored, independently checkable `.lara`
paper artifacts — its **members** — declared by one `.laramap` manifest that
gives each member a local path and a unique **alias**. Running a map rereads
every member's current bytes, rechecks each one on its own, qualifies its local
identities by its alias, merges the members into one unit, completes the
cross-member attacks, checks that unit, and prints one composite verdict with
map-relative statuses.

There is deliberately no build system in that sentence. No hashing, no
lockfile, no cache, no scheduler, no snapshot pinning — see D1.

## D1 — A map is a recheck, not a build

The manifest declares *where the members are*, and nothing about *what they
were*. A member entry is exactly an alias and a path:

```text
(member paper_a papers/a/paper.lara)
```

There is no checksum field and no generated map id. Both were considered and
rejected: a pinned hash is a second source of truth whose only possible future
is to disagree with the file it names, and whose only possible remedy is a
regeneration step — which is a build system. The identity a map does report is
the one that already exists: each member's own declared `artifact` digest, from
its replay identity, carried into the verdict unchanged (D5). If a member's
bytes changed since the last run, the map says so by producing a different
verdict, not by refusing to run.

The cost is real and accepted: a map is only as reproducible as the working
tree it is run in. That is the same contract a single `.lara` file already has.

## D2 — What v1 refuses

Excluded from v1, each because it would make the map more than a recheck:

- **nested maps** and **member imports** — a member is a leaf artifact;
- **recipes** and **network fetch** — the manifest names local paths only;
- **evidence generation** — a map never manufactures a leaf;
- **symbol substitution** and **ontology mapping** — a map never rewrites a
  member's propositions to make two members agree (see D6);
- **cross-member support imports** — no member's argument may cite another
  member's leaf or argument as a premise;
- **hand-written cross-member undercuts** — the only cross-member attacks are
  the ones saturation derives from declared contraries (D8);
- **snapshot pinning, caches, lockfiles** (D1);
- **any member with a nonempty admission or group-pruning audit** — a member
  that needed §4.3 quarantine is refused (`MRUnsupportedAdmission`), which is
  what makes `evidence-blocked` impossible in a composite verdict (D5);
- **content deduplication across members**, and **judging whether two members'
  evidence is independent** — both are outside the loader's contract. The loader
  decides *which bytes a map runs over* and nothing about what those bytes mean.
  Two members citing the same underlying study are two members: the map reports
  both, and whether that double-counts is a question for a reader or for a
  future layer with a notion of evidential provenance, not for a stage whose
  whole job is path resolution and rechecking. Recording it here because it is
  the boundary an implementer is most likely to cross by accident — a loader
  that "helpfully" collapsed duplicate content would change verdicts while
  looking like an optimisation.

Each exclusion is enforced, not merely undocumented: the first six have no
syntax to express them, the audit rule is a load-stage rejection, and the last
two are enforced by absence — the loader has no access to the notions it would
need.

## D3 — Namespace encoding: length-framed qualification

Two members may each declare a leaf `e1` and an argument `a1`. Linking them
requires an injective map from `(alias, local name)` to a linked identity, and
the map's reports require the inverse. One function does both:

```text
frame s          = show (utf8Length s) ++ ":" ++ s
qualifiedKey a l = frame a ++ frame l          -- e.g. 7:paper_a2:e1
```

This is the house convention `Lara.Strict.ND` uses for its source-atom keys,
reimplemented rather than shared: ND keeps `frame` private because its frames
are bytes of a frozen backend wire key, and a map key is a different namespace
that must be free to move without perturbing a backend's bytes. The two share a
shape, deliberately not a function.

`MemberAlias` is opaque and restricted to nonempty ASCII `[A-Za-z0-9_-]`. The
restriction is what makes the framing unambiguous to a *reader* as well as to a
parser — an alias can never contain the `:` that frames a key — and it keeps
every alias inside `Lara.Wire`'s bare-atom set, so no manifest or verdict byte
ever needs quoting for an alias. `parseQualifiedKey` is the operational
injectivity witness and is a left inverse of `qualifiedKey`; it rejects
non-canonical frame lengths, a frame that splits a UTF-8 character, and trailing
bytes, so it cannot be used to launder an arbitrary string into an identity.

There are two observers and they are not interchangeable:

| Observer | Form | May be an identity? | May appear in a verdict? |
|---|---|---|---|
| `qualifiedKey` | `7:paper_a2:e1` | yes — the only one | as a derived identity |
| `qualifiedDisplay` | `paper_a::e1` | **no** | **no** |

`QualifiedId` is opaque and carries the `(alias, local)` pair, so both
observers are total. Its `Ord` is `(alias, local)` lexicographic — **not** the
order of the framed key, which sorts by frame length first. Deterministic map
output is ordered by that instance; the key is only an identity.

**Qualified:** `LeafId`, `ArgId`, `GroupId`, and every reference to them inside
a `SupportTerm` (`SLeaf`, discharge targets), `Attack` endpoints, and `DupGroup`
membership. **Not qualified:** `Prop`/`Term` symbols, `Pred`, `FunSym`,
`RuleId`, `Param`, `QuestionId`, `ObligationId`, certificate premise positions,
`TheoryDigest`. The split is the whole design in one line: *handles* are
member-local and get qualified, *meanings* are shared and must not be — see D6.

## D4 — Manifest grammar `lara-map@1`

Exactly one top-level form. All five sections are required, in this order. No
unknown tag anywhere.

```text
(lara-map@1
  (policy   POLICY-ID PATH)
  (backends (backend BACKEND-ID VERSION) ...)
  (members  (member ALIAS PATH) ...)
  (alignments ALIGNMENT ...)
  (questions  MAPQUESTION ...))

ALIGNMENT   ::= (alignment REF REF ASSERTION (author NAME)
                           (audit-status AUDIT) (rationale TEXT))
MAPQUESTION ::= (question QUESTION-ID (refs REF REF ...) (nl TEXT))
REF         ::= (ref ALIAS CLAIM-NAME COORD)
COORD       ::= whole | (arg NAT)
ASSERTION   ::= same | different
AUDIT       ::= unreviewed | reviewed | disputed
```

The manifest carries `policy` and `backends` **explicitly** so that no member is
privileged: shared-contract validation compares every member against the
manifest, never against whichever member happened to load first (D7).

### Backend references are the wire pair, not the surface `nd@1`

A backend is spelled in both grammars as **two separate atoms** — the id and the
version — exactly as `Lara.Wire.encodeReplayId` spells it:

```text
(backend nd 1)          correct
(backend nd@1 1)        WRONG — do not "correct" it to this
```

This is deliberate and is recorded here because it looks like a typo to anyone
who has read the surface language, where a backend reference *is* written
`nd@1`. The surface `@` is a **separator**, not part of the name:
`Lara.Syntax`'s `backendRefP` parses `ident '@' version` and yields
`(BackendId "nd", "1")`, so a `BackendId` structurally never contains an `@`.
Every committed core golden agrees — `examples/A/example.core.sexp` carries
`(backends (backend nd 1))`.

The consequence is not cosmetic. A manifest spelling `nd@1` would name a backend
that no member can ever declare, so the D7 contract comparison against it could
never succeed for any member — and because the codec is deliberately
id-agnostic, nothing would fail at decode time to tell you so. The failure would
surface only as a map that rejects every member for a reason that reads like a
disagreement between them. `prop_backendSpelling` (MapWireSpec) pins the pair
form so the mistake cannot be reintroduced silently.

The alignment's `(author …) (audit-status …) (rationale …)` triple is
`Lara.AST.Binding` — the same record, with the same three spellings, that the
surface language already uses for the untrusted link between a claim's prose
and its formal target. An alignment is that kind of object one level up: an
untrusted, attributed link between two *formal* coordinates. Reusing the record
means the audit vocabulary is spelled once.

## D5 — Composite verdict grammar `map-verdict@1`

```text
(map-verdict@1
  (scope map)
  (schema lara-map-verdict@1)
  (core lara-core@0.2)
  (policy POLICY-ID)
  (backends (backend BACKEND-ID VERSION) ...)
  (members (member ALIAS PATH (artifact DIGEST)) ...)
  (nodes  (node ALIAS ARG-ID INDEX) ...)
  (labels (INDEX LABEL) ...)
  (edges  (SRC TGT) ...)
  (statuses (status ALIAS CLAIM-NAME ATOM STATUS) ...))

LABEL  ::= in | out | undec
STATUS ::= gap | justified | contested | defeated
```

- `(scope map)` leads the form so no consumer can confuse these bytes with a
  solo `(verdict …)`. It is a *decoded field*, not an unread literal, so a
  future second scope is an additive constructor rather than a silent
  reinterpretation. Both directions are tested: a solo verdict does not decode
  as a map verdict, and a map verdict does not decode as a solo one.
- `PATH` is the **manifest-spelled** path, never a resolved absolute path. This
  is enforced by the type, not by discipline: `DeclaredPath` is opaque, path
  resolution produces a plain `FilePath`, and no verdict field accepts one. Two
  people running the same manifest from different directories get byte-identical
  verdicts.
- `DIGEST` is the member's own declared `artifact` identity, carried through
  unchanged (D1).
- `ATOM` is `Lara.Wire.encodeAtom`'s form, read back by the new
  `Lara.Wire.decodeAtomSExpr`. Propositions are core objects; a second
  proposition syntax would be a second thing to keep in step with
  `lean/Lara/Driver.lean`.
- There is **no `evidence-blocked` status.** A member with a nonempty
  admission or group-pruning audit is refused at load (D2), so no query in a map
  can be blocked, and the composite verdict's status vocabulary is the plain
  four-state one.

## D6 — Alignments are checked, never applied

An alignment says two coordinates are `same` or `different`. It is a
*claim about the members*, evaluated against them; it is never a rewrite that
makes them agree. A false alignment is a map rejection (`MRAlignmentFalse`,
exit 1), not a warning and not a repair.

This is the reason symbol substitution and ontology mapping are excluded (D2).
The moment a map may rewrite a member's propositions to satisfy an alignment,
the composite verdict stops being a statement about the artifacts the authors
wrote. Two papers that use different predicate symbols for the same idea are
two papers that disagree formally, and the map's job is to report that, not to
paper over it.

A single alignment's two coordinates must select the same *kind* of target:
mixing `whole` with `(arg n)` is not a comparison anyone can state, and is
rejected rather than interpreted.

## D7 — Shared-contract equality compares structures, not names

Every member is compared against the manifest on five fields. Each failure is
`MRContract alias field` (exit 1):

| Field | Compared |
|---|---|
| `CFPolicyId` | the member's declared `policy` id vs the manifest's |
| `CFPolicyStructure` | the parsed `Lara.AST.Policy` values, by `==` |
| `CFSignature` | `unitSigma` of the elaborated units, by `==` |
| `CFTheories` | `unitTheories`, by `==` — label **and** payload |
| `CFBackends` | `sort (programBackends program)` vs the manifest list, with `sort (replayBackends rid)` machine-checked equal to it |

The primary comparand is the *program's* declared selection rather than the
replay id's, because that is what lets the whole backend check run before
elaboration, where the rest of the source-only contract fields live (D11 stage
4). The two are the same list — `sourceReplayInput` hands `programBackends`
straight to `mkReplayId` — so the move is an identity, and rather than trust
that, the elaborated half asserts `sort (replayBackends rid) == sort
(programBackends prog)` on every member. If the elaborator ever stops passing
the list through, that assertion fails loudly instead of the contract quietly
comparing the wrong thing.

`CFBackends` compares **sorted** lists, and that asymmetry is deliberate — do
not "fix" it to a positional comparison. The manifest keeps its
canonical-ascending, duplicate-free requirement (D10), because that is what
makes manifest bytes canonical: one backend selection must have exactly one
spelling. A *member*, however, is under no such rule.
`Lara.Elaborate.sourceReplayInput` sorts a program's theory digests but passes
`programBackends` through in **author declaration order**, so a member written
`use backends [ra@1, nd@1]` has `replayBackends = [(ra,"1"), (nd,"1")]`. A
positional comparison would therefore make that member's contract
*unsatisfiable* — it could never join any map — for a difference that carries no
meaning. Backend selection is a **set**: declaration order says nothing about
what was selected, so the comparison normalises it and the manifest's ordering
requirement is about bytes, not about semantics. (See also the wire-pair
spelling ruling under D4 — the two are the most common ways to get this field
wrong.)

`CFPolicyStructure` is the load-bearing one. Comparing the *parsed* policy means
comments and whitespace are already gone, so the check accepts two files that
differ only in formatting — and rejects a redefinition hiding under a shared
name, which comparing ids alone would wave through. That is the whole point of
having a shared contract: a map whose members silently ran under different rules
would produce a composite verdict that means nothing.

## D8 — Linking pipeline

```text
qualify each member's local identities
  -> merge leaves / args / attacks / queries / groups
  -> generate cross-member conflict attacks
  -> checkUnit on the linked unit
  -> grounded evaluation
  -> composite verdict
```

Structurally identical support terms across members are **merged** into one
linked argument, and every original `(alias, local ArgId)` handle is retained in
the node table pointing at the same index — so a map can always say which
members independently produced an argument.

Cross-member saturation mirrors `lean/Lara/Context/Fragment.lean`'s
`crossAttsFrom`: for each ordered pair of distinct-member checked nodes whose
conclusions form a declared contrary instance and whose target is
`conflictAttackableB`, emit the attack, deduplicate, sort deterministically.
Member-local attacks are transported unchanged. Then the ordinary `checkUnit`
runs. **Nothing is asserted; everything is checked** — the linked unit is an
ordinary unit and goes through the ordinary checker, so a map cannot accept
anything a hand-written equivalent unit would not.

## D9 — Deterministic output ordering

The composite verdict's order is fixed, so two runs and two implementations
produce the same bytes:

| Section | Order |
|---|---|
| `members` | manifest order |
| `nodes` | member order, then that member's own declaration order |
| `labels` | ascending `INDEX`, covering exactly `0 .. n-1` |
| `edges` | ascending lexicographic `(SRC, TGT)`, exactly as `buildAccept` emits |
| `statuses` | member order, then that member's own claim declaration order |

The codec **carries** this order; it does not impose it. The encoder never
sorts: the driver decides the canonical order and the bytes reflect exactly that
decision, so an ordering bug in the driver is visible in the output instead of
being hidden by a tidy-up in the printer.

## D10 — Where each rule is enforced: codec, loader, or checker

The split is:

> The codec enforces what one form's own bytes determine. The loader enforces
> what needs the members loaded. The checker enforces everything about the
> linked unit.

So the **manifest decoder** rejects: an empty `members` section; a duplicate or
ill-spelled alias; an empty path; a non-canonical `NAT` (leading `+`, leading
zero); a `backends` list that is not duplicate-free and strictly ascending by
`(id, version)`; a question relating fewer than two references; an alignment
that mixes `whole` with `(arg n)`; an unknown tag, a wrong version atom, a wrong
arity, or a trailing form.

Member-list emptiness and alias uniqueness are **owned by the decoder outright**:
they are properties of the manifest text, the decoder settles them, and there is
therefore deliberately *no* loader-stage error constructor for either. A driver
sees them as `MBWire`. Adding `MBEmptyMembers`/`MBDuplicateAlias` constructors
would be dead code that reads like a second, contradictory owner — which is
exactly the ambiguity this section exists to remove.

It does **not** resolve a path, look a claim up, or check that a reference names
a declared alias. Those get member-attributed diagnostics from the loader:
`MBUnknownAlias`, `MBUnknownClaim`, `MBCoordinateOutOfRange`, and
`MBMixedSelector` (which the loader raises for a *question's* reference list,
which the grammar leaves heterogeneous by construction). Every one of these,
codec or loader, is a boundary error and exits 2 — the split decides which
diagnostic the operator reads, never which inputs are accepted.

A **composite verdict is terminal**: no later stage will revisit it, so its
decoder additionally checks self-consistency — aliases in `nodes` and `statuses`
are declared in `members`, each `(alias, ARG-ID)` handle occurs once, `labels`
covers exactly `0 .. n-1` ascending, `edges` are strictly ascending, and every
index is in range. This mirrors the two extra invariants `Lara.Wire` already
checks at its own decode boundary (unique argument ids, declared attack
endpoints): wire well-formedness, not a checker rejection.

## D11 — Error classes, precedence, and exit codes

```text
data MapError = MapBoundary MapBoundaryError | MapReject MapRejectError
```

`MapBoundary` ⇒ exit 2 (the map is ill-formed). `MapReject` ⇒ exit 1 (the map
was understood and the answer is no). Both print exactly one line on stderr and
nothing on stdout, and no verdict is produced. Success ⇒ exit 0 with the
composite verdict on stdout (or `--out`). `mapErrorExitCode` is the single place
the 1/2 split lives; `renderMapError` is the single place the lines live.

`MapBoundaryError`: `MBWire`, `MBUnreadable`, `MBDuplicatePath`,
`MBManifestPolicySource`, `MBManifestPolicyMismatch`, `MBMemberSource`
(carrying the member's own exit-2 text), `MBDuplicateClaim`, `MBUnknownAlias`,
`MBUnknownClaim`,
`MBCoordinateOutOfRange`, `MBMixedSelector`. There is no constructor for an empty member list or a
duplicate alias: per D10 the decoder owns both, and they arrive as `MBWire`.

`MBDuplicateClaim` is the one rule here the `.lara` frontend does not also
enforce, and it is worth saying why the map has to.
`Lara.Elaborate.prepareSource` refuses a repeated `leaf`, `arg` or group id and
says nothing about a repeated `claim` id, because a solo verdict reports
statuses by *proposition*: two `claim c_pos` blocks are the same query asked
twice, and asking twice is harmless. A map reports statuses by
`(member alias, claim name)`, so the same member yields two rows under one
handle — and an alignment coordinate resolves that handle by a first-wins
`lookup`, silently picking one of them. It is a *boundary* failure rather than a
rejection because nothing has been decided about the map: the member cannot be
described in a map's vocabulary at all.

Left unrefused it was also a live cross-driver divergence, which is how it was
found. `lara check` exited 0 with the duplicated handle in its `statuses`
section, `lara map-input` emitted an envelope, and both envelope decoders then
refused those bytes — so the two drivers disagreed 0 against 2 on one map, and
the `map-input` door contradicted its own promise that every envelope it prints
is one that decodes. Fixing it at the loader rather than by relaxing the
decoders is the right direction: the decoders are correct that a repeated handle
makes a status ambiguous.

`MapRejectError`: `MRContract`, `MRUnsupportedAdmission`,
`MRMemberAdmissionStop`, `MRMemberRejected`, `MRAlignmentFalse`,
`MRLinkRejected`, `MRLinkBoundary`.

### `MRLinkRejected` has no fixture, because it cannot happen

No anchor under `test/fixtures/map/` exercises `MRLinkRejected`, and none can
be built: when every member of a map passes its own check, the linked unit is
always accepted. This used to be a review-time argument, and it is now a
theorem for the Lean driver (issue #321). `Lara.Map.Driver.linkedUnitOf_checked`
proves that the unit `linkAndEvaluate` builds is accepted by `checkUnit`
whenever each member is well-formed on its own and the aliases and leaf
identities are unique. The envelope decoder enforces the uniqueness, and the
frontend's solo check establishes the rest. A synthetic anchor built to fill
the row would therefore test the fabrication and not the system. The two
paragraphs below are the informal version of the proof.

**Generated attacks always type.** `crossMemberAttacks` emits `attackFor`'s
shape for an ordered pair only when the two conclusions contrary-match and the
target is `conflictAttackableB`. Those are the same two conditions
`Lara.Attack.checkAttackTarget` then imposes, on the same values:

- a leaf target becomes `undermine … []`, whose target check reads `Γ(l)` — and
  `Γ(l)` *is* the target's inferred conclusion, the value the saturation
  matched against;
- a rule-instance target becomes `rebut`, whose target check requires the root
  rule to be defeasible (exactly `conflictAttackableB`) and contrary-matches
  against `instAPat θ (ruleConclusion r)` — which is what `inferSupport`
  returned as that term's conclusion, so again the same value.

**Nothing else can fail either.** Duplicate rule ids, R12 policy
well-formedness and Σ well-sortedness are decided from the shared contract and
from a union of ground atoms each member already passed under that same
contract; duplicate arguments cannot arise because the merge makes the linked
terms distinct; each member's own arguments and attacks are transported by a
rename proved to preserve support and attack typing (`hasSupport_mapLeaf`,
`hasAttack_mapLeaf`, `buildGamma_qualifyGamma`); and the all-pairs
missing-conflict scan is satisfied because a same-member pair is unchanged from
the member's own accepted unit and a cross-member pair is exactly what the
saturation covers.

**What the proof covers, and what it does not.** It covers the Lean driver's
construction exactly, up to the order in which arguments and attacks are
listed. It takes three things as premises instead of deriving them from bytes:
each member's solo check (no envelope byte records that it passed), the shared
policy's scope and well-formedness, and the signature stage of the linked unit.
The Haskell driver's `MRLinkRejected` is covered by
`scripts/check-map-conformance.sh`, which compares its output with the Lean
driver's byte for byte, and not by the proof. Were the saturation's emission
condition and the attack checker's acceptance condition ever to come apart, the
proof would stop compiling. The constructor is kept because it is
`checkUnit`'s answer and a map must be able to report it, not because anything
is expected to produce it.

**D12's structural merge used to be the other region no shipped map reached,
and the two were easy to read as one.** They have different roots. The merge
was unreachable because leaf qualification confines a term collision to a
single member, so only a premise-less rule can make it fire. A link rejection is
unreachable because the saturation and the checker agree. The merge is now
reached by `test/fixtures/map/merge/`, and that map still links and is
accepted, as the theorem says it must: a co-owned term still yields attacks
that type.

### Three constructors that look foldable and are not

Each of these could plausibly be merged into a neighbour, and each is separate
on purpose. The note is here so the next reader does not simplify them back.

| Constructor | Could be folded into | Why it is separate |
|---|---|---|
| `MBManifestPolicyMismatch PolicyId PolicyId` | `MBWire` | `MBWire` means *these bytes failed to decode*, and here they decoded perfectly — the manifest names one policy id and the file it points at declares another, so the manifest is internally **inconsistent**, not malformed. Synthesising a codec error for a non-codec condition puts a fiction in the diagnostic, and the alternative — leaving it to the contract check — would blame every member in turn for a disagreement none of them caused. It exits 2 because the map cannot be said to be *about* a policy at all: the shared contract every member is compared against is exactly the pair being reported as contradictory. |
| `MBManifestPolicySource String` | `MBWire` | Same reason as the row above, and the same mistake made one level along: the manifest's bytes decoded fine and a **different file** — the policy the manifest points at — failed to parse. An `MBWire` here would name the wrong file and the wrong kind of failure. It is the manifest's counterpart to `MBMemberSource`, which has a member to attribute it to; this one does not. The *unreadable* case is not folded in either: a path the loader resolved and could not open is `MBUnreadable`, which names that resolved path. |
| `MRMemberAdmissionStop MemberAlias String` | `MRMemberRejected` or `MRUnsupportedAdmission` | Not `MRMemberRejected`: that carries a `Rejection`, and a §4.3 admission stop has **no rejection class** — there is no `R8` in `RejectClass`, which is why the solo `.lara` door prints `renderAdmissionRejection` rather than a verdict for it. Not `MRUnsupportedAdmission` either, though both are admission-caused and both exit 1: that one means the member is fine and **v1 declined to support** its pruned material ("this feature does not cover your artifact yet"), while this one means the member **genuinely fails the policy the map checks under** ("fix the artifact or the policy"). Two different remedies must not share one line. |

`MBDuplicatePath`'s third field is the **resolved** file the two aliases share,
not a `DeclaredPath`. Carrying a declared path there implicitly assumed the two
members had *spelled* the same thing; a symlink, or a relative path beside an
absolute one, breaks that assumption and leaves no single manifest spelling that
is true of both. The canonical target is the one thing that is, and only a
`FilePath` can name it — the same resolved path `MBUnreadable` already carries.
Nothing about D5 is weakened: `DeclaredPath` guards the *verdict's* bytes, and
no verdict field accepts a `MapBoundaryError`.

**Diagnostic precedence** is the pipeline order, and only the first failure is
reported:

1. manifest codec (`MBWire`) — nothing else can run until the manifest decodes;
2. the manifest's own policy file — `MBUnreadable`, then
   `MBManifestPolicySource`, then `MBManifestPolicyMismatch`. It is read before
   any member, because it *is* the shared contract and no member can be compared
   without it. None of the three is an `MBWire`: the manifest's own bytes have
   already decoded by this point;
3. manifest resolution — `MBDuplicatePath`, in member order. Emptiness and alias
   uniqueness cannot appear at this stage: stage 1 has already settled them;
4. per member, in manifest order — `MBUnreadable`, then `MBMemberSource`, then
   `MBDuplicateClaim`, then `MRContract`, then `MRMemberAdmissionStop`, then
   `MRUnsupportedAdmission`, then `MRMemberRejected`. Three things fix that
   order:

   - a member's own source boundary runs before the map's contract check, so an
     unreadable or unparseable member is never reported as a contract
     disagreement. `MBUnreadable` covers only the member's **artifact** path,
     which the manifest chose and the loader resolved; everything else about the
     member — including its co-located **policy** file, whose path comes from
     the member's own `policy` declaration — is `MBMemberSource`, under the
     member's alias. The split is *who chose the path*, not who opened the file;
   - `MBDuplicateClaim` sits between the source boundary and the contract check,
     and is above the latter for the reason the former is: a member whose claims
     cannot be named unambiguously cannot be reported on at all, so there is
     nothing for a contract disagreement to be said about. The `.lara` frontend
     does not guard this — `prepareSource` refuses a repeated leaf, argument or
     group id and not a repeated claim id — so a member reaching stage 4 may
     genuinely carry one, and it is the map, whose reporting handle is
     `(alias, claim name)`, that has to refuse it;
   - the contract check runs before **both** admission outcomes. A member can be
     contract-mismatched and quarantined at once — its policy copy carrying an
     `admission` row the manifest's copy lacks is exactly both — and the
     contract is the more basic disagreement: an admission decision taken under
     a policy that is not the map's contract says nothing about the map. This is
     why the contract check is split into a parsed-source half (`CFPolicyId`,
     `CFPolicyStructure`, `CFBackends`) that runs before elaboration and an
     elaborated half (`CFSignature`, `CFTheories`) that runs after. The three
     fields carrying the meaning need only the parsed source, so they can be
     decided first. `MRContract` therefore has two points in the pipeline, and
     only the first can fire in practice, since the elaborated pair cannot fail
     unless `CFPolicyStructure` already has;
5. reference resolution, in manifest order — `MBUnknownAlias`,
   `MBUnknownClaim`, `MBCoordinateOutOfRange`, `MBMixedSelector`;
6. linking — `MRLinkBoundary`, then `MRLinkRejected`;
7. alignment evaluation — `MRAlignmentFalse`, at the lowest-numbered failing
   alignment.

Boundary stages precede reject stages wherever both could fire, so an operator
never sees exit 1 for a map that was also ill-formed. Inside the verdict codec,
`labels` is decoded before `nodes` and `edges` because it pins `n`; a defect in
`labels` therefore reports as a labels error even when a node index is also out
of range.

## Rejected alternatives

**A lockfile or content-addressed member store.** Rejected as D1 — it converts a
recheck into a build, and every failure mode it introduces (stale pin, missing
object, regeneration step) is a failure mode a recheck simply does not have. The
cost of the rejection is that a map is only as reproducible as its working tree;
that cost is already paid by every single `.lara` file.

**A generated map id.** Rejected for the same reason plus one more: an id
derived from the members' bytes would have to change whenever any member
changed, so it could not name "this map" across revisions — which is the only
thing anyone would want an id for.

**Growing `Lara.Wire.Tag` with the map keywords.** Rejected. That table is
frozen, byte-pinned by conformance goldens, and textually mirrored by
`lean/Lara/Driver.lean`; adding non-core spellings to it would put the map's
vocabulary inside the frozen core and force the Lean mirror to grow with every
map grammar change. `Lara.Map.Wire` has its own `MapTag` closed sum with its own
single `mapTagToString` table. The two overlap on spellings (`policy`,
`backend`, `status`, …) *deliberately* — the map names the same concepts with
the same words — but the tables are independent, and a collision-freedom
property covers each separately.

**Sharing `Lara.Strict.ND`'s `frame`/`renderFrames`.** Rejected as D3 — those
frames are bytes of a frozen backend wire key. The map reimplements the shape
and pins its own bytes with a golden.

**Symbol substitution or an ontology layer to reconcile members.** Rejected as
D6. It would make the composite verdict a statement about a rewritten corpus
rather than about the artifacts the authors wrote.

**Privileging the first member's policy as the map's contract.** Rejected as D7.
It makes the map's meaning depend on manifest order, and it silently demotes
every other member to a conformance test against an arbitrary peer. The manifest
states the contract; every member is compared to it symmetrically.

**Reusing `PublicStatus` (with `evidence-blocked`) in the composite verdict.**
Rejected as D5. Because a member with a nonempty admission audit is refused
outright, the blocked case is unreachable, and carrying a status the grammar can
never emit would invite a consumer to handle a state that does not exist.

**A single `Index` newtype for both alignment coordinates and linked-unit
argument indices.** Rejected. They name different things, and a shared type
would make swapping them a silent bug. `ArgIndex` and `NodeIndex` are separate
opaque newtypes, per the repo's rule that separate namespaces get separate
types.

**Overloading `lara deps` to report a map's inputs.** Rejected: `lara deps`
already means *checked certificate dependencies* — what the accepted unit's
strict steps cited — and a map's inputs are a different question with a
different answer shape (which files were read, not which certificates were
relied on). Overloading the name would make the same command mean two things
depending on the extension it was handed, which is exactly the ambiguity
`depsMap`'s refusal exists to prevent. The intended future interface is a
separate `lara inputs` plus depfiles, which is what an incremental build needs
and what `lara deps` deliberately is not; nothing here implements it, and
nothing here should be read as promising it on a schedule.

## D12 — What qualification renames, and what the merge is for

`Lara.Map.Qualify` renames `LeafId`, `ArgId` and `GroupId` and every reference
to them; D3's second list is what it leaves alone. Two consequences of that
split were discovered while implementing it, and both are recorded here because
each looks like a defect until the reason is stated.

**The structural merge is unreachable under the shipped policies, and is
implemented anyway.** D8 says structurally identical support terms from different
members are merged into one linked argument. Under leaf qualification a term that
*mentions a leaf* can only collide with a term of the same member — and a member's
own unit has already passed `firstDuplicate`. So the merge can only fire on a
**leaf-free** term, i.e. an instance of a premise-less rule, which neither
`empirical-v1` nor `agreement-v1` has. It is implemented, exported as
`Lara.Map.Link.mergeArguments`, and tested two ways: directly on synthesized
terms, and through a real map. `test/fixtures/map/merge/` runs under
`convention-v1`, a fixture policy with one premise-less rule, and both of its
members declare the same leaf-free argument (issue #316). That map is a
conformance anchor like any other, so both drivers are shown to fold the two
handles onto one index — the composite's `nodes` section carries
`(node paper_adopt conv 0) (node paper_critic conv 0)` — and to agree on every
byte. Deleting the merge would make the linked unit's freedom from duplicate
arguments depend on a property of the *policy* rather than of the linker, and
it is what forces attack endpoints to be re-pointed at a term's canonical
identity. The fixture exercises that too: the critic's declared rebuttals name
its own copy of the merged argument, and are re-pointed at the adopter's.

D11's `MRLinkRejected` note records the other region no shipped policy reaches.
The two are neighbours and not one argument, and the distinction matters when
either is revisited: adding a premise-less rule makes *this* one fire, and would
not by itself make a link rejection possible.

**Saturation generates for cross-member pairs only.** D8's `crossAttsFrom` mirror
runs over ordered pairs of checked nodes *from different members*, never over a
same-member pair. That restriction is not an optimisation. A same-member
attackable contrary pair is already covered by that member's own declarations —
its solo check ran the same all-pairs scan and either found the pair covered or
rejected the member — and an extra generated attack for it would not be inert: a
root rebut covers every argument containing the target, where the member's own
undercut at a position covers less. Generating it would add edges the author never
declared and the solo verdict never had, which is exactly what "a map is a
recheck, not a rewrite" forbids.

**The Lean mirror reuses `Lara.Strict`'s framing; the Haskell deliberately does
not.** D3 records why `Lara.Map.Types` reimplements `frame`/`renderFrames`: ND's
frames are bytes of a frozen backend wire key. `lean/Lara/Map/Qualify.lean` has no
such constraint — it states no byte — and what it needs is
`Lara.Strict.decodeFrames_render`, an already-proved round-trip. The two spellings
agree (`Nat.repr s.utf8ByteSize ++ ":" ++ s` on both sides), so one proof serves
both, and `qualifiedKey_inj` is the mechanized counterpart of `parseQualifiedKey`.

**There is no monotonicity theorem, and there will not be one.** Grounded status
is not preserved when a framework is extended, so nothing in this development says
a member's claim keeps its solo status inside a map.
`lean/Lara/Map/Link.lean`'s `linkMembers_status_not_preserved` exhibits the
failure instead: two *accepted* maps differing by one member, in which one claim
atom is `justified` and then `defeated`. That non-preservation is the reason a map
is worth computing at all (D3's cross-framework reading), so it is exhibited
rather than apologised for.

## D13 — `--out` is a product file, not a stdout redirect

`lara check <file> --out <path>` writes the verdict to `path` through
`Lara.AtomicWrite.atomicWriteFile`, so a `Makefile` rule can name a verdict file
as its output. Two decisions fix what that means: `--out` **atomically replaces
the output only on success**, and a failure **returns nonzero and leaves the
previous file intact**.

1. **`path` is replaced when and only when the check accepts.** Every nonzero
   exit leaves the previous `path` byte-for-byte as it was. A caller that
   ignores the exit code therefore reads a *stale* answer rather than a
   *corrupted* one, and the same-directory temporary plus rename means a
   concurrent reader sees either the old bytes or the new ones and never a
   partial write.
2. **A failure otherwise behaves exactly as it does without the flag.** A
   rejected solo unit still prints its `(verdict … reject …)` on stdout; a
   refused map still prints its one `renderMapError` line on stderr and no
   verdict. `--out` names where an *accepted* verdict goes, and nothing else
   about the command moves. A caller wanting a rejection's bytes in a file uses
   the default form and redirects.

A write that cannot complete — a nonexistent or unwritable directory, a
destination that *is* a directory — exits **2**, not 1. That is a
filesystem-boundary failure of the command, in the same class as an unreadable
input, and not a statement about the artifact; conflating it with 1 would let a
caller read "the map was rejected" out of "the disk is full". It is also the one
exit the flag *adds*: without `--out` that same run would have exited 0 with a
verdict on stdout. `Lara.AtomicWrite`'s `bracketOnError` removes the temporary
on that path, so a failed write leaves neither a damaged destination nor a stray
file (`test/MapExampleSpec.hs`, `prop_outFailedWriteLeavesNothingBehind`).

**Two properties of the write that a `--out` caller does not choose**, recorded
because `--out` reuses `Lara.AtomicWrite` — written for *generated repository
artifacts* — against an arbitrary user-named path:

- **The destination ends up `0644`.** `atomicWriteWith` sets that mode on its
  temporary before the rename, so a `0600` destination comes back `0644` (a
  widening) and a restrictive `umask` is ignored for a new one. `--out` is not
  for a path whose mode matters.
- **A symlink destination is replaced, not followed.** `rename(2)` acts on the
  link, so `--out` at a symlink leaves a regular file there and the former
  target's bytes untouched. Ordinary POSIX behaviour, worth stating because it
  silently breaks a link a `make map-check OUT=` user set up deliberately.

Neither was changed. Narrowing them means a second write path, or altering a
helper `Lara.BindingAudit` and `scripts/claim-support.hs` depend on for exactly
the behaviour it has — and both are the *right* behaviour for the generated
artifacts that helper exists to write. If `--out` ever needs to preserve a
destination's mode, that is a new writer, not an edit to this one.

The Make wrapper is correspondingly small, and **phony**:

```make
MAP ?= examples/agreement-map-multi/map.laramap
map-check:
	cabal run exe:lara -- check "$(MAP)" $(if $(OUT),--out "$(OUT)",)
```

Phony is the D1 rule expressed in Make. A map is a recheck, so this target must
run whenever it is invoked; a real file target keyed on member timestamps would
report a stale answer for exactly the edit D1 promises is picked up — one that
preserves mtime.

## What is settled, and what is not

`Lara.Map.Qualify` and `Lara.Map.Link` have landed, with their Lean counterparts
`lean/Lara/Map/Qualify.lean` (the rename's injectivity, its disjointness across
aliases, and its transport through `HasSupport`, `HasAttack`, `CheckedProgram`,
`edgeB`, `checkedAF`, `labelC` and `statusC`) and `lean/Lara/Map/Link.lean` (the
N-member fold, proved to preserve `Lara.Context.SideOk`, closed through
`Lara.Context.link_checked`, and with both of that theorem's hygiene premises
proved rather than assumed). The two are discharged from different things, and
the difference matters: `foldHygiene_of_distinct_aliases` discharges
`FoldHygiene` from **alias distinctness alone**, while
`linkMembers_declared_nodup` also takes **each member's own `Nodup`** as a
hypothesis. Alias distinctness settles the cross-member half — two members
cannot collide after qualification — and says nothing about a member colliding
with itself, which the loader establishes per member before any of them becomes
linkable.

Between them they settle qualification, the merge, the linked check and the
grounded evaluation for the fold. Neither driver runs the fold. Both build the
linked unit in one batch, saturating every cross-member pair over the fully
merged argument list. Since issue #321 that batch has its own theorems, in
`lean/Lara/Map/Batch.lean` and `lean/Lara/Map/Link.lean`:

- `Lara.Map.batch_checked` proves the batch unit is accepted. It is stated for
  any duplicate-free argument list and any attack list with the right members,
  so it holds for both drivers' merge order and attack de-duplication.
- `batch_atts_mem_iff_fold` and `batch_args_mem_iff_fold` prove that the batch
  and the fold produce the same attacks and the same arguments. The fold
  computes each step's conclusions under the environment accumulated so far,
  the batch under the whole map's. The step that reconciles them is that a
  member's argument has the same conclusion in every environment that extends
  the member's own, and that is where member well-formedness and alias hygiene
  are used. The equivalence takes one premise that `batch_checked` does not:
  every member carries the shared policy. The fold reads each member's own
  policy at every step, so the premise belongs to the fold, and
  `linkMembers_checked` already takes it. A real map always satisfies it,
  because the loader compares every member to the manifest's one contract (D7).
- `Lara.Map.Driver.linkedUnitOf_checked` applies `batch_checked` to the Lean
  driver's own linked unit. The driver's generator now calls the same
  `crossPairs` function the theorem is about, and its output bytes did not
  change.

Two things stay outside the proofs: each member's solo check, which no envelope
byte records, and the Haskell driver, which `scripts/check-map-conformance.sh`
ties to the Lean driver byte for byte.

`Lara.Map.Driver` and `lean/Lara/Map/Driver.lean` have since landed too, and with
them reference resolution (`MBUnknownAlias`, `MBUnknownClaim`,
`MBCoordinateOutOfRange`, and a question's `MBMixedSelector`) and alignment
evaluation (`MRAlignmentFalse`), which consume the same coordinates and did land
together as this record said they would. `lara check <file.laramap>` is the
third CLI door, printing `map-verdict@1` bytes on acceptance and one
`renderMapError` line at `mapErrorExitCode`'s 2-or-1 on failure; the `.lara` and
`.sexp` doors are untouched, and every extension neither arm names still reaches
the wire door.

### The parity envelope `map-check-input@1`

The Lean driver has no `.lara` parser, no `.laramap` parser, and no manifest to
resolve paths against, so it cannot be handed what the Haskell driver is handed.
It is given a **checked-boundary parity envelope** instead — the map's policy id
and backend selection, each member's alias, manifest-spelled path, declared
`artifact` digest, claim names paired with their propositions, and elaborated
`unit` in `Lara.Wire.encodeUnit`'s existing form, plus the declared alignments —
and performs the qualification, the merge, the cross-member saturation,
`checkUnit`, the grounded evaluation and the alignment assertions **itself**. It
never reads a Haskell verdict. `lara map-input <file.laramap>` emits the
envelope, `scripts/check-map-conformance.sh` byte-compares the two drivers'
stdout and exit codes over `test/fixtures/map/`, and `make cross-check` runs it
(no longer the required CI; see `docs/ci-scope-decision.md`).

Four rulings about it, each of which looks arbitrary without its reason:

- **It is not a user-facing artifact format and not a snapshot.** `lara check
  map.laramap` never reads one, and nothing in the production path from a
  manifest to a verdict passes through these bytes. It carries elaborated units
  rather than paths precisely because it is a comparison anchor rather than a
  thing to re-run.
- **It carries the members' own units, not a pre-linked one.** A driver handed a
  linked unit would only be re-checking someone else's merge, and the linking is
  the thing under comparison.
- **It has its own tag table on both sides.** `Lara.Map.Driver.EnvTag` and
  `lean/Lara/Map/Driver.lean`'s `MTag` are separate types from
  `Lara.Map.Wire.MapTag`, overlapping it on most spellings, for the reason this
  record already gives for keeping `MapTag` out of `Lara.Wire.Tag`: the two map
  grammars above are frozen and a debugging aid must be free to move without
  perturbing them.
- **Its decoder settles what its own bytes determine**, exactly as the composite
  verdict's does, because it too is terminal input: nonempty members with unique
  aliases, ascending duplicate-free backends, per-member claim-name uniqueness,
  agreement of every member's unit with the first on the shared policy sections,
  and alignment coordinates that resolve. What it deliberately does *not* do is
  reconstruct a `CheckedMembers`: that type is a promise about files that were
  read and rechecked, and no byte string can make it. A decoded
  `MapCheckInput` is ordinary derived data and is never a way back into the
  production path.

### The two decoders were audited side by side, not just fixture-tested

A harness whose two sides accept different *languages* can agree on every
committed fixture and still be wrong about every case nobody wrote, so the two
envelope decoders were compared condition by condition rather than only run over
the corpus. Two divergences were found that way and are fixed: an **empty member
path** (Haskell required nonempty via `mkDeclaredPath`, Lean did not — it
produced a full verdict where the other refused) and a **duplicate leaf id**
(neither wire decoder scans a unit's leaves for repeats, so it reached the
envelope decoder, and only one of them refused it).

Ten further probes — a quoted non-ASCII alias, a quoted alias with a space, an
empty alias, an alias containing a dot, an empty artifact digest, an empty claim
name, an empty policy id, an empty backend id, a leading-zero `(arg 00)`, and an
`(arg n)` past 64 bits — were spliced into the committed envelope and put through
both decoders. All ten **agree**. The non-ASCII alias is the one worth keeping as
a fixture and now is one (`malformed/non-ascii-alias.sexp`): it must be written
as a *quoted* atom to test anything, because a bare non-ASCII atom dies in each
driver's lexer before the alias rule is consulted, and the two spellings of that
rule are independent (`isAscii c && isAlphaNum c` against `Char.isAlphanum`,
which agree only because the latter is ASCII-only).

Three fields are **symmetrically permissive**: an empty `artifact` digest, an
empty policy id and an empty backend id are accepted by both. That is not a
divergence and is deliberately left alone — it matches what the `lara-map@1`
manifest decoder accepts in the same positions, and tightening the envelope
alone would make it reject material the manifest can legitimately produce.

The one thing the envelope cannot carry is a *pre-boundary* failure. A map whose
manifest is malformed, whose member is unreadable, whose member disagrees with
the shared contract, or whose coordinates do not resolve never reaches the
checked boundary, so no envelope exists and there is nothing to hand the Lean
driver. The conformance harness records those anchors as `pre-boundary` and
checks the one thing that is comparable: that both Haskell doors agree the map
never got that far, and that neither printed a verdict.

Two things are known and deliberately deferred, recorded here so a later
increment budgets them rather than discovering them.

**Linking is quadratic in the declared arguments.** `SupportTerm` has structural
`Eq` and no `Ord`, so `mergeArguments`, `renameTable` and the attack `dedupe` all
scan lists rather than consult a map, and `crossMemberAttacks` is an all-pairs
loop over the conclusion cache — which the checker's own conflict scan is too. A
map's argument count is bounded by what its members declared, so nothing here is
a problem at the sizes a `.laramap` reaches today; it is recorded because the
fix, an `Ord` instance or a hash of the canonical term encoding, is a change to
the *core* AST and therefore has to be budgeted rather than slipped in.

**The two implementations break the shared-section tie differently.**
`Lara.Map.Link.sharedSections` reads Σ, rules, contraries, exceptions, theories
and the group mode off the **first** member and asserts every other member
agrees. `lean/Lara/Map/Link.lean`'s `linkStep` takes them from the **incoming**
member, so a folded side carries the **last** member's. Under the agreement
premise both modules run behind — every member compared to the manifest, D7 —
the two are the same values, so this is not a divergence in behaviour. It is
recorded because it is a divergence in *code*, and a future reader checking one
mirror against the other should know the tie-break is deliberate on both sides
rather than a bug in one.

**The disagreement arms are unreachable, and therefore untested.**
`sharedSections`'s six comparisons and `linkedLeaves`'s and `linkedArguments`'
duplicate guards are all guards on invariants D7 and D3 already establish. They
are checked rather than assumed (see the modules' own notes), but no test drives
them, because reaching one means constructing a `CheckedMembers` that
`Lara.Map.Load` cannot produce.

**One coverage gap at the map level remains.** Of the three this record listed
before the driver landed, two are closed: `test/fixtures/map/agreement` is a
three-member map, and the permutation property is `MapSpec`'s
`prop_memberPermutationPermutesReport` — reordering the manifest permutes
`members`, `nodes` and `statuses` and renumbers the framework, and the
`(alias, claim, status)` answer set is unchanged. All three orderings are
asserted as *sequences* rather than as multisets, which is what makes "member
order" in D9 a tested claim.

Its companion `prop_aliasRenamingPreservesStatuses` covers the other half:
renaming every alias changes the alias half of every handle the verdict reports
— the member records' and, the load-bearing one, the node table's, whose alias
sets across the two runs are asserted disjoint — and changes no claim's status.
The local argument id inside a handle is deliberately *not* expected to move: it
is the member's own name for its own argument, and renaming the member does not
rename that.

The identifier-level fact behind that second property is mechanized:
`statusC_mapLeafProg` (`lean/Lara/Map/Qualify.lean`) proves that a uniform
injective leaf rename of an accepted program preserves a claim's status. It is
**not** an instantiation of the shipped property, and should not be read as one:
nothing connects two independent `linkMap` runs under two alias assignments to a
single application of `mapLeafProg`, so the end-to-end statement is carried by
the test and the identifier-level one by the proof.

**The interaction of the merge with a real policy used to be untested**, for the
reason D12 gives: neither shipped policy has a premise-less rule, so no shipped
map can reach the structural merge. It is tested now. `test/fixtures/map/merge/`
reaches the merge through `linkMap` (`MapLinkSpec`'s
`prop_mergeFiresThroughAMap`) and through both drivers
(`scripts/check-map-conformance.sh`), with its goldens pinned fresh beside the
agreement map's (issue #316).

**Three follow-ups recorded from the driver increment's reviews, since
resolved.** Each was tracked as an issue: #316, #317 and #318 respectively.

1. **Two more conformance anchors: resolved** (issue #316). The review asked for
   a map in which the structural merge fires and for a cross-driver *link
   rejection*. The first now exists: `test/fixtures/map/merge/` runs under a
   fixture policy with a premise-less rule, and both drivers agree on it (see
   D12). The second cannot exist. `linkedUnitOf_checked` proves that a map whose
   members each pass their own check always links to an accepted unit (see the
   `MRLinkRejected` note under D11). So the gate gained one anchor, and the
   link-rejection row is settled by proof instead of by a fixture.

2. **Three helpers were triplicated: resolved** (issue #317). `sameSelectorKind`,
   `firstDuplicate` and `strictlyAscending` now each have exactly one
   definition, in `Lara.Map.Types`, beside the `Coord` type the first one is
   about. `Lara.Map.Wire`, `Lara.Map.Driver`, `Lara.Map.Load` and the
   `mkMapManifest` smart constructor all call those. The tag *tables* stay split
   on purpose, because the grammars must be free to move independently. These
   three were never tables, so one definition couples no vocabulary. The copies
   were behaviourally identical: the move changed no test outcome.

3. **`withTree`'s temporary directory name was predictable: resolved** (issue
   #318). It used to be derived from a deleted `openTempFile` marker plus a fixed
   suffix, and `createDirectoryIfMissing` then adopted whatever was at that
   path, a planted symlink included. The four map test modules (`MapSpec`,
   `MapLoadSpec`, `MapLinkSpec`, and `MapExampleSpec`, which carried a fourth
   copy) now share one helper, `test/Lara/TempTree.hs`. It reserves the directory
   with `mkdtemp(3)`: one atomic call, mode `0700`, and it fails rather than
   adopt an existing path. No dependency was added, because `unix` was already a
   test-suite dependency.

`Lara.Source.Load` and `Lara.Map.Load` have since landed, and between them they
settle everything about *which bytes a map runs over*: the `.lara` source-loading
seam is now shared with the CLI rather than living inside it, member paths
resolve against the manifest's own directory, two aliases resolving to one file
are refused, each file is read once per invocation, and every member is
rechecked solo and compared to the manifest's shared contract before it becomes
linkable. Reference resolution (`MBUnknownAlias`, `MBUnknownClaim`,
`MBCoordinateOutOfRange`, and a question's `MBMixedSelector`) is deliberately
*not* in the loader: it needs each member's claim list, which the loader hands
onward, and it belongs beside the alignment evaluation that consumes the same
coordinates.

**Inherited: `.laramap` manifests are read with locale decoding.** The loader
reads a manifest through `readFile`, so the process locale decides how its bytes
become text; a manifest containing non-ASCII under a non-UTF-8 locale can fail to
read or read differently. This is *not* introduced by the map: it is exactly what
the existing `.lara` door does, and the map's loader shares that door's reading
seam on purpose, so changing it here would make the two doors disagree. The raw
`.sexp` door already avoids it by reading bytes and letting invalid UTF-8 become
a located codec error. Aligning the text doors on the same treatment is a
separate change to the `.lara` boundary, with its own diagnostics to settle, and
is deliberately not bundled into this increment.

**The `decodeNodes` coverage gap is closed.** This record previously assigned it
to the driver increment, and the driver increment did it.

`decodeNodes` used to check that every node index was *in range* but not that
the nodes *covered* every labelled index, so a verdict with two labels and an
empty `nodes` section decoded. It no longer does: the decoder now requires
`Set.fromList (map mnIndex nodes) == Set.fromList (map fst labels)`, the
invariant is documented on `MapVerdict.mvNodes`, and `MapWireSpec`'s round-trip
generator derives its nodes as a surjection onto the label indices rather than
from independent choices — which is what had made the gap invisible, since a
generator that never produced a non-covering table could never notice one being
accepted.

The condition is not arbitrary strictness. Every linked argument exists
*because* some member declared its support term, so a labelled index with no
handle would describe an argument that arose from nobody: unproducible, and
unattributable if it somehow appeared. Two malformed rows pin it — one dropping
the only node that names an index, one emptying the section outright — and the
first is the sharper, because every node it leaves behind is still unique and
still in range.

It was done at the driver increment rather than deferred for a reason worth
recording: the tightening was only *meaningful* once something produced node
tables, and the moment one existed it was also free. Every verdict
`Lara.Map.Driver` emits satisfies the condition, so no fixture and no golden
moved. Deferring past that point would have meant paying for it later with
bytes that had drifted in the meantime.

### The shipped D3 map, and what the example is evidence of

`examples/agreement-map-multi/` is the record's worked example: the D3
agreement map (issue #64) rewritten as four independently authored,
independently checkable artifacts under one `map.laramap`. It is registered
three ways, and each registration buys something different.

* Each member directory is an **ordinary worked example** in
  `Lara.WorkedExamples.workedExamples`, so it carries the same derived
  `example.core.sexp` and `expected.json` every other example does, gets the
  same freshness assertion, and is run through both *solo* drivers by
  `scripts/differential.sh`. That is what makes "each member stands alone" a
  checked fact rather than a claim in a header comment.
* The **map** is an anchor of `scripts/check-map-conformance.sh`, whose
  anchor discovery now spans two roots. Both drivers compute the composite
  independently and agree on its bytes.
* The composite is compared, in `test/MapExampleSpec.hs`, against the **legacy
  single-file oracle** `examples/agreement-map/`, which stays in the tree
  byte-unchanged. Same labels, same edge set, same four propositions, same four
  statuses, under the stated node correspondence `pa=0, pb=1, pc=2, pd=3`.

The last of those is the point of the whole increment, and it is worth being
precise about *why* it is not a tautology. The legacy artifact **declares** both
rebut edges by hand, because all four papers live in one file and each can name
the other's argument. No member of the map declares either edge, and none could:
`pb` is another artifact's argument, unnameable from paper A. The two edges in
the composite are **generated** by cross-member saturation from the declared
contrary pair — and the pair whose setting index differs still gets no edge,
which is the feature D3 exists to demonstrate. So the two answers agreeing is
two different computations reaching the same result, not one computation read
twice.

What the example is **not** evidence of: the verdict *bytes* are not equal and
are not meant to be (D5). A composite leads with `(scope map)`
and reports each status under its `(member alias, claim name)` handle, so a
consumer can never mistake it for a solo `(verdict …)`. The paper contents and
the declared `artifact` digests are illustrative reconstructions, as everywhere
in `examples/`; a digest is author-declared metadata carried through unchanged,
never a checksum of the member's bytes (D1).

**The manifest's expected-verdict comment is checked, not deleted** (issue
#320). `map.laramap` ends with an `EXPECTED COMPOSITE VERDICT` comment: the
verdict's `nodes`, `labels`, `edges` and `statuses` sections, with each status
row cut to its `(alias claim status)` handle. It is the first statement of the
example's answer a reader meets, and a comment survives every change that
regenerates `map.verdict.sexp`, so left alone it goes stale without anyone
noticing. Two fixes were weighed:

- **Rejected: delete the block and point readers at `map.verdict.sexp`.** That
  golden is already test-checked, but it is a separate file of wire bytes, and
  the manifest is where a reader looks first.
- **Chosen: keep the block and check it.** `MapExampleSpec`'s
  `prop_manifestVerdictCommentIsCurrent` parses the block and compares it with
  the sections the live run encodes. A pipeline change that moves the verdict
  therefore fails a test instead of leaving a wrong answer in the example.

The cost is a constraint on the comment's layout. The lines between the
banner's closing rule and the first bare `;` line must parse as S-expressions,
and every malformed shape fails the property by name. Explanatory prose belongs
after that bare `;` line, which the parser does not read.
