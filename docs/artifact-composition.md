# Maps of independently checked artifacts

This reference defines the composition layer: its vocabulary, the two grammars and their codecs, loading, qualification, linking, the `.laramap` driver, `--out`, and the worked example. The layer is strictly additive above the core: no corpus unit, mutant, wire, replay-identity or golden byte depends on it, and its only core-side surface is two exports of an existing `Lara.Wire` production. The composite verdict is `map-verdict@2` over `lara-core@0.3`. Code and other documents cite sections by stable `D1` to `D14` labels; [Legacy section identifiers](#legacy-section-identifiers) maps each to its section. This reference is the companion to [`docs/spec.md`](spec.md) §12 and its versioned extension marker, [`strict-certificates.md#1-one-seam-for-opaque-strict-certificates`](strict-certificates.md#1-one-seam-for-opaque-strict-certificates) for the shared-contract fields a member is compared on, and [`rejection-surface.md`](rejection-surface.md) for the two-exit-code door story a map inherits.

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

## A map is a recheck, not a build

The manifest declares *where the members are*, and nothing about *what they
were*. A member entry is exactly an alias and a path:

```text
(member paper_a papers/a/paper.lara)
```

There is no checksum field and no generated map id. A pinned hash is a second
source of truth that can only disagree with the file it names, and only a
regeneration step, which is a build system, could reconcile them. An id derived
from the members' bytes would change whenever any member changed, so it could
not name "this map" across revisions. The identity a map does report is
the one that already exists: each member's own declared `artifact` digest, from
its replay identity, carried into the verdict unchanged (D5). If a member's
bytes changed since the last run, the map says so by producing a different
verdict, not by refusing to run.

A map is therefore only as reproducible as the working tree it is run in. That
is the same contract a single `.lara` file has.

## What v1 refuses

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
  whole job is path resolution and rechecking. A loader that collapsed
  duplicate content would change verdicts while looking like an optimisation.

Each exclusion is enforced, not merely undocumented: the first six have no
syntax to express them, the audit rule is a load-stage rejection, and the last
two are enforced by absence — the loader has no access to the notions it would
need.

## Namespace encoding: length-framed qualification

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

## Manifest grammar `lara-map@1`

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

The surface language writes a backend reference `nd@1`, but the surface `@` is
a **separator**, not part of the name:
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
form.

The alignment's `(author …) (audit-status …) (rationale …)` triple is
`Lara.AST.Binding` — the same record, with the same three spellings, that the
surface language already uses for the untrusted link between a claim's prose
and its formal target. An alignment is that kind of object one level up: an
untrusted, attributed link between two *formal* coordinates. Reusing the record
means the audit vocabulary is spelled once.

## Composite verdict grammar `map-verdict@2`

```text
(map-verdict@2
  (scope map)
  (schema lara-map-verdict@2)
  (core lara-core@0.3)
  (policy POLICY-ID)
  (backends (backend BACKEND-ID VERSION) ...)
  (members (member ALIAS PATH (artifact DIGEST)) ...)
  (nodes  (node ALIAS ARG-ID INDEX) ...)
  (labels (INDEX LABEL) ...)
  (edges  (SRC TGT) ...)
  (statuses (status ALIAS CLAIM-NAME ATOM STATUS) ...)
  HOLES?)

HOLES  ::= (holes (hole ALIAS ARG-ID (obligations QUESTION-ID ...+)) ...+)
LABEL  ::= in | out | undec
STATUS ::= gap | justified | contested | defeated
```

Decoders accept exactly `@2`; a `map-verdict@1` envelope or schema is refused
(D14).

- `INDEX`, `SRC` and `TGT` are **AF indices** of the linked unit; `nodes`,
  `labels` and `edges` share that one space (D14). The type of a verdict index,
  `NodeIndex`, is a distinct opaque newtype from `ArgIndex`, the type of an
  alignment coordinate's `(arg n)`, because the two name different things.

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
- `ATOM` is `Lara.Wire.encodeAtom`'s form, read back by
  `Lara.Wire.decodeAtomSExpr`. Propositions are core objects; a second
  proposition syntax would be a second thing to keep in step with
  `lean/Lara/Driver.lean`.
- There is **no `evidence-blocked` status.** A member with a nonempty
  admission or group-pruning audit is refused at load (D2), so no query in a map
  can be blocked, and the composite verdict's status vocabulary is the plain
  four-state one. Carrying a status the grammar can never emit would invite a
  consumer to handle a state that does not exist.

Both map grammars spell their keywords through `Lara.Map.Wire`'s own `MapTag`
closed sum and its single `mapTagToString` table, separate from
`Lara.Wire.Tag`. The core table is frozen, byte-pinned by conformance goldens
and textually mirrored by `lean/Lara/Driver.lean`, so map keywords stay out of
it. The two tables share spellings such as `policy`, `backend` and `status`
where they name the same concepts, and a collision-freedom property covers each
separately.

## Alignments are checked, never applied

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

## Shared-contract equality compares structures, not names

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
4). The two are the same list, since `sourceReplayInput` hands `programBackends`
straight to `mkReplayId`, and rather than trust that, the elaborated half
asserts `sort (replayBackends rid) == sort (programBackends prog)` on every
member. If the elaborator stopped passing the list through, that assertion
would fail loudly instead of the contract quietly comparing the wrong thing.

`CFBackends` compares **sorted** lists, not positions. The manifest keeps its
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
spelling rule under D4 — the two are the most common ways to get this field
wrong.)

`CFPolicyStructure` is the load-bearing one. Comparing the *parsed* policy means
comments and whitespace are already gone, so the check accepts two files that
differ only in formatting — and rejects a redefinition hiding under a shared
name, which comparing ids alone would wave through. That is the whole point of
having a shared contract: a map whose members silently ran under different rules
would produce a composite verdict that means nothing.

## Linking pipeline

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
members independently produced an argument. A handle whose linked argument is a
located hole is retained in the `holes` section instead (D14), and the index a
node carries is the AF index.

Cross-member saturation mirrors `lean/Lara/Context/Fragment.lean`'s
`crossAttsFrom`: for each ordered pair of distinct-member checked nodes whose
conclusions form a declared contrary instance and whose target is
`conflictAttackableB`, emit the attack, deduplicate, sort deterministically.
Member-local attacks are transported unchanged. Then the ordinary `checkUnit`
runs. **Nothing is asserted; everything is checked** — the linked unit is an
ordinary unit and goes through the ordinary checker, so a map cannot accept
anything a hand-written equivalent unit would not.

## Deterministic output ordering

The composite verdict's order is fixed, so two runs and two implementations
produce the same bytes:

| Section | Order |
|---|---|
| `members` | manifest order |
| `nodes` | member order, then that member's own declaration order |
| `labels` | ascending `INDEX`, covering exactly `0 .. n-1` |
| `edges` | ascending lexicographic `(SRC, TGT)`, exactly as `buildAccept` emits |
| `statuses` | member order, then that member's own claim declaration order |
| `holes` | member order, then that member's own declaration order (the `nodes` handle order); omitted when empty |

The codec **carries** this order; it does not impose it. The encoder never
sorts: the driver decides the canonical order and the bytes reflect exactly that
decision, so an ordering bug in the driver is visible in the output instead of
being hidden by a tidy-up in the printer.

## Where each rule is enforced: codec, loader, or checker

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
therefore *no* loader-stage error constructor for either. A driver sees them as
`MBWire`; a loader constructor for either would be dead code and a second,
contradictory owner.

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
covers exactly `0 .. n-1` ascending, `edges` are strictly ascending, every
index is in range, and `nodes` covers every labelled index. The coverage rule
holds because every linked argument exists only because some member declared
its support term, so a labelled index with no handle would describe an argument
that arose from nobody. Two malformed rows pin it: one drops the only node that
names an index, leaving every remaining node unique and in range, and one
empties the section. This mirrors the two extra invariants `Lara.Wire` already
checks at its own decode boundary (unique argument ids, declared attack
endpoints): wire well-formedness, not a checker rejection.

## Error classes, precedence, and exit codes

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
described in a map's vocabulary at all. The envelope decoders refuse a repeated
handle for the same reason, so refusing it at the loader keeps `lara check` and
`lara map-input` in agreement and keeps every envelope `map-input` prints
decodable.

`MapRejectError`: `MRContract`, `MRUnsupportedAdmission`,
`MRMemberAdmissionStop`, `MRMemberRejected`, `MRAlignmentFalse`,
`MRLinkRejected`, `MRLinkBoundary`.

### `MRLinkRejected` has no fixture, because it cannot happen

No anchor under `test/fixtures/map/` exercises `MRLinkRejected`, and none can
be built: when every member of a map passes its own check, the linked unit is
always accepted. For the Lean driver this is a theorem:
`Lara.Map.Driver.linkedUnitOf_checked` proves that the unit `linkAndEvaluate` builds is accepted by `checkUnit`
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

### Three constructors kept separate from their neighbours

Each of these sits beside a constructor it could be mistaken for, and names a
different condition.

| Constructor | Neighbour | Why it is separate |
|---|---|---|
| `MBManifestPolicyMismatch PolicyId PolicyId` | `MBWire` | `MBWire` means *these bytes failed to decode*, and here they decoded perfectly — the manifest names one policy id and the file it points at declares another, so the manifest is internally **inconsistent**, not malformed. Synthesising a codec error for a non-codec condition puts a fiction in the diagnostic, and the alternative — leaving it to the contract check — would blame every member in turn for a disagreement none of them caused. It exits 2 because the map cannot be said to be *about* a policy at all: the shared contract every member is compared against is exactly the pair being reported as contradictory. |
| `MBManifestPolicySource String` | `MBWire` | Same reason as the row above, and the same mistake made one level along: the manifest's bytes decoded fine and a **different file** — the policy the manifest points at — failed to parse. An `MBWire` here would name the wrong file and the wrong kind of failure. It is the manifest's counterpart to `MBMemberSource`, which has a member to attribute it to; this one does not. The *unreadable* case is not folded in either: a path the loader resolved and could not open is `MBUnreadable`, which names that resolved path. |
| `MRMemberAdmissionStop MemberAlias String` | `MRMemberRejected` or `MRUnsupportedAdmission` | Not `MRMemberRejected`: that carries a `Rejection`, and a §4.3 admission stop has **no rejection class** — there is no `R8` in `RejectClass`, which is why the solo `.lara` door prints `renderAdmissionRejection` rather than a verdict for it. Not `MRUnsupportedAdmission` either, though both are admission-caused and both exit 1: that one means the member is fine and **v1 does not support** its pruned material ("this feature does not cover your artifact yet"), while this one means the member **genuinely fails the policy the map checks under** ("fix the artifact or the policy"). Two different remedies must not share one line. |

`MBDuplicatePath`'s third field is the **resolved** file the two aliases share,
not a `DeclaredPath`. A declared path there would assume the two members had
*spelled* the same thing; a symlink, or a relative path beside an absolute one,
breaks that assumption and leaves no single manifest spelling that
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

## Located holes in a linked unit

`lara-core@0.3` (`docs/theory-core.md#holes-located-gaps-and-term-level-critical-questions`) accepts a unit containing a
*located hole*: an argument that type-checks with a nonempty mandatory
obligation set. A hole is declared but is never an AF node. A map member may
carry one, and so may the linked unit, which `checkUnit` accepts. Because holes
are not AF nodes, linked declaration positions and AF indices diverge as soon as
a hole precedes a complete argument, so every index in the verdict is an AF
index.

**Version.** The envelope tag is `map-verdict@2` and the schema
`lara-map-verdict@2`. Both decoders accept exactly `@2`. Holes need no new
input: the manifest grammar `lara-map@1` and the parity envelope
`map-check-input@1` carry no hole field, because a member's unit already
carries its `open` questions.

**One index space.** Every `INDEX` in `nodes`, `labels` and `edges` is an AF
index. `nodes` lists exactly the handles whose linked argument is complete,
each at the AF index of that argument, reached through the checker's
AF-to-declaration map (`cuNodeDecls` / `nodeDecls`). The decoder's coverage rule
(every labelled index has a handle) applies to that space.

**Holes by member handle.** The optional `holes` section lists one row per
`(member alias, member-local ARG-ID)` handle whose linked argument is a hole,
with the hole's exact mandatory root obligations in the core's
`collectObligations` order. It carries no index: a hole has no AF index, and
its linked declaration position is an artifact of the merge that no reader can
resolve. A merged hole — one term declared by several members, possible only
for a leaf-free term (D12) — gets one row per handle, each with the same
obligations, exactly as a merged node gets one `nodes` row per handle.

**Order: handle order, as for `nodes`.** Rows are in member order, then that
member's own declaration order — the restriction of the one handle list both
sections come from — so the rows of a merged hole need not be adjacent. This is
the rule `nodes` and `statuses` follow, a reader scanning one member finds that
member's rows in the order its author wrote them, and it agrees with linked
declaration order whenever the merge does not fire.

**Section placement and canonical form.** `holes` follows `statuses` and is
omitted when the linked unit has no hole; a present-but-empty section is
refused, as the solo verdict refuses one (`docs/theory-core.md#wire-the-holes-section`).
The decoder also refuses a row of the wrong shape, an undeclared alias, an
empty or duplicated obligation list entry, and a handle that appears twice
across `nodes` and `holes` together (a handle is a node or a hole, once). It
cannot check that a row's obligations are the ones its member's term carries,
or that rows are in handle order: both need the members.

**The saturation generates nothing that touches a hole.** The cross-member
generator ranges over the complete conclusion cache (`conclusionCache` in
Haskell, `Lara.Context.conclusionCache` in Lean), so it emits no attack
sourced at or aimed at a hole, for four reasons:

- an attack sourced at a hole is checked but inert (located-gap D4), so
  generating one would add bytes to the linked unit and no edge;
- the missing-conflict scan ranges over complete pairs only, so no attack onto
  a hole is ever required for acceptance;
- a generated rebut of a hole's root could only reach a complete argument
  containing that root, and such an argument inherits the hole's obligations
  and is itself a hole (located-gap D6), so it adds no edge; a generated
  undermine targets a leaf, which is never a hole;
- the generator stays the one `Lara.Map.batch_checked_holes` is proved about.
  That theorem takes members that may carry holes
  (`SideOkHoles`, located-gap D9), and `batch_checked` is its hole-free
  corollary.

`Lara.Map.crossPairs_endpoints_complete` and its driver instance
`Lara.Map.Driver.generatedAttacksOf_endpoints_complete` mechanize the
consequence: both endpoints of every generated attack type with an empty
obligation set. A member's own *declared* attacks that touch a hole are
transported unchanged and go through the ordinary checker (D8): typed, and
inert when sourced at a hole.

**What is proved about a map with holes.** The driver's acceptance of a linked
unit with holes is covered by a composition theorem as well as by `checkUnit`. `Lara.Map.Driver.linkedUnitOf_checked_holes` accepts the Lean
driver's linked unit whenever each member satisfies `SideOkHoles` in its own
environment. `Lara.Map.Driver.generatedAttacksOf_live` reads
`crossPairs_endpoints_complete` through the checker: every generated attack is
compiled, and neither of its endpoints is a hole.
`Lara.Map.Driver.linkedUnitOf_hole_report` says each hole of the accepted
unit is some member's declaration. Any member that declares it gives it, in
that member's own environment, exactly the reported conclusion and obligation
set. The hole rows read their obligations from those records, so a row repeats
the member's solo report: linking adds and drops no obligation.
`Lara.Map.batch_member_hole_reported` gives the converse at the batch level,
where every member hole is reported. These are statements about the accepted
unit. The `holes` wire section, its order and its handle selection are covered
by the parity script, not by these theorems.

**No attack list on a hole row.** The solo verdict's hole row lists the attacks
the hole sources by original attack declaration index. A map has no
reader-facing attack index — the linked attack list mixes transported and
generated attacks and is never printed — and every such attack is inert, so the
map row carries none. A reader who needs them reads the member's own solo
verdict. The same holds for obligation sites (`theory-core.md#holes-located-gaps-and-term-level-critical-questions` D12):
the solo row locates each obligation at its rule occurrences, the map row
names the obligations only.

**Statuses keep their four-state form.** A map status is read off the linked
unit's complete support. A claim whose own member supports it only by a hole
can still be `justified` in the map when another member contributes complete
support for the same proposition; `test/MapSpec.hs`'s merged-hole case pins
this.

**Evidence.** `test/fixtures/map/hole/` is a committed accepting anchor whose
two members each declare a hole, one of them before the member's complete
argument, so the index spaces diverge; `scripts/check-map-conformance.sh`
compares its `map-verdict@2` bytes across the Haskell and Lean drivers.
`test/MapWireSpec.hs` carries a golden vector with a `holes` section, the
generator emits holes, and the malformed-verdict matrix covers the section.

## What qualification renames, and what the merge is for

`Lara.Map.Qualify` renames `LeafId`, `ArgId` and `GroupId` and every reference
to them; D3's second list is what it leaves alone. Two consequences of that
split each look like a defect until the reason is stated.

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
members declare the same leaf-free argument. That map is a
conformance anchor like any other, so both drivers are shown to fold the two
handles onto one index — the composite's `nodes` section carries
`(node paper_adopt conv 0) (node paper_critic conv 0)` — and to agree on every
byte. Deleting the merge would make the linked unit's freedom from duplicate
arguments depend on a property of the *policy* rather than of the linker, and
it is what forces attack endpoints to be re-pointed at a term's canonical
identity. The fixture exercises that too: the critic's declared rebuttals name
its own copy of the merged argument, and are re-pointed at the adopter's.

D11's `MRLinkRejected` note covers the other region no shipped policy reaches,
and the two have different roots. The merge is rare because leaf qualification
confines a term collision to a single member, so only a premise-less rule makes
it fire. A link rejection is impossible because the saturation and the checker
agree, so the merge map links and is accepted: a co-owned term
yields attacks that type.

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

**There is no monotonicity theorem, because none holds.** Grounded status is not
preserved when a framework is extended, so nothing in this development says a
member's claim keeps its solo status inside a map.
`lean/Lara/Map/Link.lean`'s `linkMembers_status_not_preserved` exhibits the
failure instead: two *accepted* maps differing by one member, in which one claim
atom is `justified` and then `defeated`. That non-preservation is the reason a map
is worth computing at all (D3's cross-framework reading), so it is exhibited
rather than apologised for.

## `--out` is a product file, not a stdout redirect

`lara check <file> --out <path>` writes the verdict to `path` through
`Lara.AtomicWrite.atomicWriteFile`, so a `Makefile` rule can name a verdict file
as its output. Two rules fix what that means: `--out` **atomically replaces
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

**Two properties of the write that a `--out` caller does not choose** follow
from `--out` reusing `Lara.AtomicWrite`, which exists to write *generated
repository artifacts*, against an arbitrary user-named path:

- **The destination ends up `0644`.** `atomicWriteWith` sets that mode on its
  temporary before the rename, so a `0600` destination comes back `0644` (a
  widening) and a restrictive `umask` is ignored for a new one. `--out` is not
  for a path whose mode matters.
- **A symlink destination is replaced, not followed.** `rename(2)` acts on the
  link, so `--out` at a symlink leaves a regular file there and the former
  target's bytes untouched. This is ordinary POSIX behaviour, and it breaks a
  link a `make map-check OUT=` user set up.

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

## Mechanized guarantees and conformance

`Lara.Map.Qualify` and `Lara.Map.Link` have Lean counterparts:
`lean/Lara/Map/Qualify.lean` (the rename's injectivity, its disjointness across
aliases, and its transport through `HasSupport`, `HasAttack`, `CheckedProgram`,
`edgeB`, `checkedAF`, `labelC` and `statusC`) and `lean/Lara/Map/Link.lean` (the
N-member fold, proved to preserve `Lara.Context.SideOk` and
`Lara.Context.SideOkHoles`, closed through `Lara.Context.link_checked` and
`Lara.Context.link_checked_holes`, and with both of that theorem's hygiene premises
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
merged argument list. That batch has its own theorems, in
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
  driver's own linked unit. The driver's generator calls the same
  `crossPairs` function the theorem is about.

Two things stay outside the proofs: each member's solo check, which no envelope
byte records, and the Haskell driver, which `scripts/check-map-conformance.sh`
ties to the Lean driver byte for byte.

`Lara.Map.Driver` and `lean/Lara/Map/Driver.lean` carry reference resolution
(`MBUnknownAlias`, `MBUnknownClaim`, `MBCoordinateOutOfRange`, and a question's
`MBMixedSelector`) together with alignment evaluation (`MRAlignmentFalse`),
which consumes the same coordinates. `lara check <file.laramap>` is the third
CLI door, printing composite verdict bytes (`map-verdict@2`) on acceptance and
one `renderMapError` line at `mapErrorExitCode`'s 2-or-1 on failure; every
extension neither the `.lara` nor the `.laramap` arm names reaches the wire
door. `lara deps` refuses a `.laramap`: it reports the checked certificate
dependencies of an accepted unit, and which files a map read is a different
question with a different answer shape.

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
(outside the required CI; see `docs/implementation.md#ci-and-local-gates`).

Four properties of it, each with its reason:

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
  `Lara.Map.Wire.MapTag`, overlapping it on most spellings, for the reason
  `MapTag` is separate from `Lara.Wire.Tag`: the two map grammars above are
  frozen and a debugging aid must be free to move without perturbing them.
- **Its decoder settles what its own bytes determine**, exactly as the composite
  verdict's does, because it too is terminal input: nonempty members with unique
  aliases, ascending duplicate-free backends, per-member claim-name uniqueness,
  agreement of every member's unit with the first on the shared policy sections,
  and alignment coordinates that resolve. What it deliberately does *not* do is
  reconstruct a `CheckedMembers`: that type is a promise about files that were
  read and rechecked, and no byte string can make it. A decoded
  `MapCheckInput` is ordinary derived data and is never a way back into the
  production path.

### The two envelope decoders accept one language

A harness whose two sides accept different *languages* can agree on every
committed fixture and still be wrong about every case nobody wrote, so the two
envelope decoders are meant to agree condition by condition, not only over the
corpus. Both refuse an **empty member path** and a **duplicate leaf id**;
neither wire decoder scans a unit's leaves for repeats, so the envelope decoder
does. The fixture `malformed/non-ascii-alias.sexp` writes its alias as a
*quoted* atom, because a bare non-ASCII atom dies in each driver's lexer before
the alias rule is consulted. The two spellings of that rule are independent
(`isAscii c && isAlphaNum c` against `Char.isAlphanum`) and agree because the
latter is ASCII-only.

Three fields are **symmetrically permissive**: an empty `artifact` digest, an
empty policy id and an empty backend id are accepted by both. That matches what
the `lara-map@1` manifest decoder accepts in the same positions, and tightening
the envelope alone would make it reject material the manifest can legitimately
produce.

The one thing the envelope cannot carry is a *pre-boundary* failure. A map whose
manifest is malformed, whose member is unreadable, whose member disagrees with
the shared contract, or whose coordinates do not resolve never reaches the
checked boundary, so no envelope exists and there is nothing to hand the Lean
driver. The conformance harness records those anchors as `pre-boundary` and
checks the one thing that is comparable: that both Haskell doors agree the map
never got that far, and that neither printed a verdict.

### Loading

`Lara.Source.Load` and `Lara.Map.Load` decide *which bytes a map runs over*:
the `.lara` source-loading seam is shared with the CLI rather than living inside
it, member paths resolve against the manifest's own directory, two aliases
resolving to one file are refused, each file is read once per invocation, and
every member is rechecked solo and compared to the manifest's shared contract
before it becomes linkable. Reference resolution (`MBUnknownAlias`,
`MBUnknownClaim`, `MBCoordinateOutOfRange`, and a question's `MBMixedSelector`)
is *not* in the loader: it needs each member's claim list, which the loader
hands onward, and it belongs beside the alignment evaluation that consumes the
same coordinates.

### Limits

**Linking is quadratic in the declared arguments.** `SupportTerm` has structural
`Eq` and no `Ord`, so `mergeArguments`, `renameTable` and the attack `dedupe` all
scan lists rather than consult a map, and `crossMemberAttacks` is an all-pairs
loop over the conclusion cache — which the checker's own conflict scan is too. A
map's argument count is bounded by what its members declared, so this is not a
problem at the sizes a `.laramap` reaches. The fix, an `Ord` instance or a hash
of the canonical term encoding, is a change to the *core* AST.

**The two implementations break the shared-section tie differently.**
`Lara.Map.Link.sharedSections` reads Σ, rules, contraries, exceptions, theories
and the group mode off the **first** member and asserts every other member
agrees. `lean/Lara/Map/Link.lean`'s `linkStep` takes them from the **incoming**
member, so a folded side carries the **last** member's. Under the agreement
premise both modules run behind — every member compared to the manifest, D7 —
the two are the same values, so this is a divergence in code and not in
behaviour, and the tie-break is deliberate on both sides.

**The disagreement arms are unreachable, and therefore untested.**
`sharedSections`'s six comparisons and `linkedLeaves`'s and `linkedArguments`'
duplicate guards are all guards on invariants D7 and D3 already establish. They
are checked rather than assumed (see the modules' own notes), but no test drives
them, because reaching one means constructing a `CheckedMembers` that
`Lara.Map.Load` cannot produce.

**`.laramap` manifests are read with locale decoding.** The loader reads a
manifest through `readFile`, so the process locale decides how its bytes become
text; a manifest containing non-ASCII under a non-UTF-8 locale can fail to read
or read differently. This is exactly what the `.lara` door does, and the map's
loader shares that door's reading seam on purpose, so the two doors agree. The
raw `.sexp` door avoids it by reading bytes and letting invalid UTF-8 become a
located codec error; giving the text doors the same treatment is a change to the
`.lara` boundary, with its own diagnostics.

### Test coverage at the map level

`test/fixtures/map/agreement` is a three-member map, and `MapSpec`'s
`prop_memberPermutationPermutesReport` checks that reordering the manifest
permutes `members`, `nodes` and `statuses` and renumbers the framework while
the `(alias, claim, status)` answer set is unchanged. All three orderings are
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

The structural merge under a real policy is reached by `test/fixtures/map/merge/`
through `linkMap` (`MapLinkSpec`'s `prop_mergeFiresThroughAMap`) and through
both drivers (`scripts/check-map-conformance.sh`); see D12.

### The shipped D3 map, and what the example is evidence of

`examples/agreement-map-multi/` is this reference's worked example: the D3
agreement map rewritten as four independently authored,
independently checkable artifacts under one `map.laramap`. It is registered
three ways, and each registration buys something different.

* Each member directory is an **ordinary worked example** in
  `Lara.WorkedExamples.workedExamples`, so it carries the same derived
  `example.core.sexp` and `expected.json` every other example does, gets the
  same freshness assertion, and is run through both *solo* drivers by
  `scripts/differential.sh`. That is what makes "each member stands alone" a
  checked fact rather than a claim in a header comment.
* The **map** is an anchor of `scripts/check-map-conformance.sh`, whose
  anchor discovery spans two roots. Both drivers compute the composite
  independently and agree on its bytes.
* The composite is compared, in `test/MapExampleSpec.hs`, against the **legacy
  single-file oracle** `examples/agreement-map/`, which stays in the tree
  byte-unchanged. Same labels, same edge set, same four propositions, same four
  statuses, under the stated node correspondence `pa=0, pb=1, pc=2, pd=3`.

The last of those is not a tautology. The legacy artifact **declares** both
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

**The manifest's expected-verdict comment is checked.**
`map.laramap` ends with an `EXPECTED COMPOSITE VERDICT` comment: the
verdict's `nodes`, `labels`, `edges` and `statuses` sections, with each status
row cut to its `(alias claim status)` handle. It is the first statement of the
example's answer a reader meets, and a comment survives every change that
regenerates `map.verdict.sexp`, so unchecked it would go stale.
`MapExampleSpec`'s `prop_manifestVerdictCommentIsCurrent` parses the block and
compares it with the sections the live run encodes, so a pipeline change that
moves the verdict fails a test instead of leaving a wrong answer in the example.

The check constrains the comment's layout. The lines between the
banner's closing rule and the first bare `;` line must parse as S-expressions,
and every malformed shape fails the property by name. Explanatory prose belongs
after that bare `;` line, which the parser does not read.

## Legacy section identifiers

Code comments and other documents cite sections of this reference by these labels.

| Label | Section |
| --- | --- |
| `D1` | [A map is a recheck, not a build](#a-map-is-a-recheck-not-a-build) |
| `D2` | [What v1 refuses](#what-v1-refuses) |
| `D3` | [Namespace encoding: length-framed qualification](#namespace-encoding-length-framed-qualification) |
| `D4` | [Manifest grammar `lara-map@1`](#manifest-grammar-lara-map1) |
| `D5` | [Composite verdict grammar `map-verdict@2`](#composite-verdict-grammar-map-verdict2) |
| `D6` | [Alignments are checked, never applied](#alignments-are-checked-never-applied) |
| `D7` | [Shared-contract equality compares structures, not names](#shared-contract-equality-compares-structures-not-names) |
| `D8` | [Linking pipeline](#linking-pipeline) |
| `D9` | [Deterministic output ordering](#deterministic-output-ordering) |
| `D10` | [Where each rule is enforced: codec, loader, or checker](#where-each-rule-is-enforced-codec-loader-or-checker) |
| `D11` | [Error classes, precedence, and exit codes](#error-classes-precedence-and-exit-codes) |
| `D12` | [What qualification renames, and what the merge is for](#what-qualification-renames-and-what-the-merge-is-for) |
| `D13` | [`--out` is a product file, not a stdout redirect](#--out-is-a-product-file-not-a-stdout-redirect) |
| `D14` | [Located holes in a linked unit](#located-holes-in-a-linked-unit) |
