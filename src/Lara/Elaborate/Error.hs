-- | The elaborator's located-ish failure type and its renderer.
--
-- Split out of "Lara.Elaborate.Internal" so the @lara-syntax\@0.5@ surface
-- passes ("Lara.Elaborate.ValueBinding" and "Lara.Elaborate.Comparison") and
-- the structural lowering can share errors without an import cycle.
-- 'Lara.Elaborate.Internal' re-exports both names, so every existing importer
-- is unaffected.
--
-- __Every__ author-facing failure of the elaborator is a constructor here.
-- That is deliberate (plan §6.1.1, decision 7A): a backend helper such as
-- 'Lara.Strict.Cell.premiseCell' is reused for /extraction/ only, and its
-- backend-worded @Left String@ never reaches an author — a surface
-- cell-obligation failure is 'ComparisonCellObligation' or 'NlCellObligation',
-- which name the offending leaf.
module Lara.Elaborate.Error
  ( ElabError (..)
  , elabErrorMessage
  ) where

import Lara.AST
import Lara.Prop (Prop, Term, prettyProp, prettyTerm)
import Lara.Syntax (polarityStr, relationStr)
import Lara.Sigma (SortFault (..), sortText)

-- | A located-ish elaboration failure. Each constructor names the offending
-- argument, rule, leaf, claim, comparison, or position so the caller can render
-- a diagnostic (see 'elabErrorMessage'). The elaborator is deterministic, so
-- the /first/ error in declaration order is the one reported.
data ElabError
  = -- | @programPolicy prog@ ≠ @policyId policy@ (the header-match invariant).
    PolicyIdMismatch PolicyId PolicyId
  | -- | a @by r(…)@ names a rule absent from the policy: @arg@, @rule@.
    UnknownRule ArgId RuleId
  | -- | the number of inferred references differs from the rule's premise count.
    ThetaReferenceCountMismatch ArgId RuleId Int Int
  | -- | an inferred reference names neither a declared leaf nor a prior argument.
    ThetaReferenceUnresolved ArgId RuleId Int ArgRef
  | -- | an inferred reference names both a declared leaf and prior argument.
    ThetaReferenceAmbiguous ArgId RuleId Int ArgRef
  | -- | the selected reference proposition does not match the premise pattern.
    ThetaReferenceShapeMismatch ArgId RuleId Int ArgRef Prop
  | -- | a repeated inferred parameter receives incompatible terms.
    ThetaReferenceConflict ArgId RuleId Int ArgRef Param Term Term
  | -- | a prior argument reference has no derivable conclusion.
    ThetaReferenceConclUnderivable ArgId RuleId Int ArgRef
  | -- | a rule parameter is absent from every inferred premise binding.
    ThetaParameterUnbound ArgId RuleId Param
    -- * Named certificate premise slots (@lara-syntax\@0.6@, #105; @\@0.8@, #131)
    --
    -- | Each names the citing @arg@, the certificate backend and version,
    -- and the offending reference as structured identifiers. The renderer
    -- alone constructs the author's @beta\@version@ spelling. The scope
    -- extends the one 'ThetaReferenceUnresolved' and 'ThetaReferenceAmbiguous'
    -- police — declared leaves and prior arguments — with the citing rule's
    -- declared premise labels (@\@0.8@, #131), but the failures are their own
    -- family because a certificate cites a /premise slot of one instance/,
    -- not a θ position, and the author's fix differs.
    --
    -- The two constructors that speak about the name /classes/ also carry the
    -- citing 'RuleId': whose labels were consulted is part of the answer.
  | -- | the reference names no premise label of the citing rule, no declared
    -- leaf, and no prior argument.
    CertSlotUnresolved ArgId BackendId Int ArgRef RuleId
  | -- | the reference names both a declared leaf and a prior argument.
    CertSlotAmbiguous ArgId BackendId Int ArgRef
  | -- | the reference names both a premise label of the citing rule and a
    -- declared leaf or prior argument (#131). Rejected even when the two
    -- classes agree on the slot: one collision policy, no carve-outs.
    CertSlotLabelAmbiguous ArgId BackendId Int ArgRef RuleId
  | -- | the reference resolves, but to nothing this instance takes as a premise.
    CertSlotNotAPremise ArgId BackendId Int ArgRef
  | -- | the named premise fills multiple slots, so the name cannot say which:
    -- the first two witnesses, 0-based — the same numbering the author writes
    -- back into @(prem N)@, so these are /not/ converted at the message
    -- boundary. The final flag says whether every matching slot has a premise
    -- label, so the renderer advertises the label repair only when it is
    -- available for whichever matching slot the author intended.
    CertSlotMultiSlot ArgId BackendId Int ArgRef Int Int Bool
  | -- | a reference atom that is neither a canonical numeral nor a source
    -- identifier, such as @007@ or @-1@.
    CertSlotNonCanonicalNumeral ArgId BackendId Int ArgRef
  | -- | the payload does not match the backend's declared premise-reference
    -- schema yet carries a symbolic reference. A symbolic name is never valid
    -- wire there, so the certificate is rejected here rather than handed to a
    -- backend that must refuse it (the dead-wire rule).
    CertSlotSchemaMismatch ArgId BackendId Int ArgRef
    -- * Named natural-deduction proof terms (@lara-syntax\@0.9@, #132;
    -- formula annotations @lara-syntax\@0.10@, #144)
  | CertNdBinderUnbound ArgId BackendId Int ArgRef
  | CertNdBinderShadowed ArgId BackendId Int ArgRef
  | CertNdBinderShadowsPremise ArgId BackendId Int ArgRef
  | CertNdMalformedBinder ArgId BackendId Int ArgRef
  | CertNdNonCanonicalIndex ArgId BackendId Int ArgRef
  | CertNdKernelIndex ArgId BackendId Int ArgRef
  | CertNdPremOutOfRange ArgId BackendId Int ArgRef Integer Int
  | CertNdFormulaMalformed ArgId BackendId Int ArgRef
  | CertNdResidualNamed ArgId BackendId Int ArgRef
  | -- | positional θ length ≠ the rule's parameter count: @arg@, @rule@,
    -- expected, got.
    ArityMismatch ArgId RuleId Int Int
  | -- | no declared leaf\/prior-arg conclusion @≡@ the ground premise: @arg@,
    -- @rule@, 1-based premise index, the ground premise proposition.
    UnresolvedPremise ArgId RuleId Int Prop
  | -- | ≥2 declared conclusions @≡@ the ground premise: @arg@, @rule@, premise
    -- index, the ground premise, and the matching leaf\/arg ids.
    AmbiguousPremise ArgId RuleId Int Prop [String]
  | -- | a @discharge q with ref@ whose @ref@ names neither a declared leaf nor
    -- a prior arg: @arg@, @question@, the reference. The renderer is the only
    -- place the source identifier is unwrapped.
    UnresolvedDischarge ArgId QuestionId ArgRef
  | -- | a @discharge q with ref@ whose @ref@ names /both/ a declared leaf and a
    -- prior arg (#129): @arg@, @question@, the reference. The one collision
    -- policy shared with 'ThetaReferenceAmbiguous' and 'CertSlotAmbiguous' —
    -- a shadowed discharge target is never silently resolved to the leaf.
    AmbiguousDischarge ArgId QuestionId ArgRef
  | -- | a @supports(c)@ over a declared claim whose term conclusion ≠ the claim
    -- formal: @arg@, @claim@, @concl(w)@, @claimFormal(c)@.
    ConclusionMismatch ArgId PropId Prop Prop
  | -- | a @status c@ whose @c@ is not a declared claim.
    UnknownStatusClaim PropId
  | -- | a @challenges(…)@ whose target arg\/leaf is not declared (diagnostic
    -- only; never affects the 'Unit').
    ChallengeTargetUndeclared ArgId
  | -- | two surface @arg@ declarations share an id (R14 well-formedness).
    DuplicateArgId ArgId
  | -- | a surface attack names an argument id that is not declared (R14
    -- well-formedness): the first undeclared endpoint in attack order.
    AttackEndpointUndeclared ArgId
  | -- | two @group@ declarations share an id (R14 well-formedness): the id.
    DuplicateGroupId GroupId
  | -- | a @group@ repeats a member (R14 well-formedness): @group@, the member.
    GroupRepeatedMember GroupId LeafId
  | -- | a @group@ has fewer than two members, so it cannot report a conflict
    -- (R14 well-formedness): the group id.
    GroupTooFewMembers GroupId
  | -- | a @group@ member is not a declared leaf (R14 well-formedness): @group@,
    -- the undeclared member.
    GroupMemberUndeclared GroupId LeafId
    -- * Policy well-formedness for premise labels (grammar App. B.4)
  | -- | a non-empty premise-label vector is not aligned one-for-one with the
    -- rule's premises (@rule@, label entries, premises).
    PremiseLabelCountMismatch RuleId Int Int
  | -- | one rule labels two premises the same (@rule@, the label).
    PremiseLabelDuplicate RuleId PremiseLabel
  | -- | a premise label spells one of §7's terminal markers @rule@\/@leaf@,
    -- which would make @a2.leaf.leaf@ parse two ways (@rule@, the label).
    PremiseLabelReserved RuleId PremiseLabel
  | -- | a premise label also names one of the same rule's critical questions,
    -- so an attack-path segment could resolve two ways (@rule@, the label).
    PremiseLabelQuestionCollision RuleId PremiseLabel
    -- * Attack-path name resolution (grammar App. B.5)
  | -- | a non-integer attack-path segment matches neither a premise label nor a
    -- question id of the targeted rule: source arg, target arg, the segment.
    AttackStepUnresolved ArgId ArgId String
    -- * @let@ value-binding elaboration (grammar App. C.2)
  | -- | two bindings share a name (defensive for hand-built ASTs).
    DuplicateValueBinding ValueName
  | -- | a hand-built binding uses the reserved interpolation head @cell@.
    ReservedValueName ValueName
  | -- | a binding name collides with a constructor already declared by Σ.
    ValueNameConstructorCollision ValueName
  | -- | a binding RHS is not a well-sorted ground term under Σ.
    ValueBindingSortError ValueName SortFault
  | -- | substitution makes an ordinary claim formal ill-sorted.
    ValueBindingClaimSortError PropId SortFault
  | -- | a one-token @nl@ interpolation names no declared value.
    NlValueBindingMissing PropId ValueName
    -- * @nl@ interpolation (grammar App. B.6)
  | -- | an @nl@ string opens @{@ without a closing @}@: the claim.
    NlUnterminatedBrace PropId
  | -- | an @nl@ string carries an unescaped @}@ (write @}}@): the claim.
    NlStrayBrace PropId
  | -- | an @nl@ string carries a @{…}@ that is not a recognized directive:
    -- the claim and the directive body as written.
    NlUnknownDirective PropId String
  | -- | @{cell l}@ names an @l@ that is not a declared leaf: the claim, @l@.
    NlCellLeafUndeclared PropId LeafId
  | -- | @{cell l}@ names a leaf failing the premise-cell obligation (exactly
    -- one numeric literal): the claim, @l@.
    NlCellObligation PropId LeafId
    -- * @comparison@ expansion (grammar App. B.3); located by the block's
    -- declared sub-claim id
  | -- | the measurand after @on@ is not declared by the policy (App. B.1).
    ComparisonUndeclaredMeasurand PropId MeasurandId
  | -- | the measurand after @on@ is declared but carries no polarity clause
    -- (App. B.1). Polarity is @Num@-gated and optional since @lara-core\@0.2@
    -- opened the sort slot (#89 D-1), so a measurand can be well-formed and
    -- still be unusable as a comparison key.
    ComparisonMeasurandNoPolarity PropId MeasurandId
  | -- | the policy declares no @comparison-scheme@ for the block's
    -- (relation, polarity) pair (App. B.2).
    ComparisonNoScheme PropId Relation Polarity
  | -- | the selected scheme names a rule the policy does not declare.
    ComparisonSchemeRuleUnknown PropId RuleId
  | -- | the scheme's @recheck@ rule is not strict.
    ComparisonRecheckNotStrict PropId RuleId
  | -- | the scheme's @recheck@ rule lists no @ord\@1@ certifier.
    ComparisonRecheckCertifierMissing PropId RuleId
  | -- | the scheme's @bridge@ rule is not defeasible.
    ComparisonBridgeNotDefeasible PropId RuleId
  | -- | the @bridge@ rule's conclusion pattern is not 4-ary over four distinct
    -- rule parameters (the favored-system-first convention, App. B.2 / F4).
    ComparisonBridgeConclusionShape PropId RuleId
  | -- | the bridge does not have exactly one premise admitting the generated
    -- comparison and one admitting the named binding leaf.
    ComparisonBridgePremiseShape PropId RuleId
  | -- | the @recheck@ rule's conclusion pattern is not a 2-ary comparison atom,
    -- so the certificate's two @(prem i)@ slots cannot be derived.
    ComparisonRecheckConclusionShape PropId RuleId
  | -- | the @recheck@ rule writes its conclusion in the opposite direction to
    -- the one the measurand's @polarity@ declares (App. B.2): the claim, the
    -- recheck rule, and the declared polarity. The scheme is internally
    -- consistent but externally backwards — it would certify the opposite of
    -- what the polarity means (grammar §1.2's hazard).
    ComparisonSchemeDirectionMismatch PropId RuleId Polarity
  | -- | the authored conclusion after @:@ is not a 2-ary system pair.
    ComparisonConclusionShape PropId Prop
  | -- | the authored conclusion's predicate ≠ the bridge conclusion pattern's:
    -- the authored head, then the bridge rule's.
    ComparisonConclusionPredMismatch PropId RuleId Pred Pred
  | -- | @result@ or @baseline@ names something that is not a declared leaf.
    ComparisonLeafUndeclared PropId LeafId
  | -- | @binding@ names something that is not a declared leaf. (Never
    -- generated: the attestation leaf stays a human claim, App. B.3.)
    ComparisonBindingNotLeaf PropId LeafId
  | -- | @binding@ names a declared leaf that the selected bridge rule's
    -- binding premise does not admit.
    ComparisonBindingNotAdmitted PropId LeafId RuleId
  | -- | @result@ and @baseline@ name the same leaf.
    ComparisonSameLeaf PropId LeafId
  | -- | @result@ or @baseline@ names a leaf failing the premise-cell obligation
    -- (exactly one numeric literal). Never the backend's wording (7A).
    ComparisonCellObligation PropId LeafId
  | -- | a named leaf matches no premise pattern of the @recheck@ rule.
    ComparisonNoPremiseSlot PropId RuleId LeafId
  | -- | a named leaf matches more than one premise slot of the @recheck@ rule.
    ComparisonAmbiguousPremiseSlot PropId RuleId LeafId [Int]
  | -- | @result@ and @baseline@ resolve to the same premise slot.
    ComparisonSlotClash PropId RuleId Int
  | -- | one-way matching bound a rule parameter twice, inconsistently: the
    -- baseline leaf, the result leaf, the parameter, and the two terms (App.
    -- B.2's inherited same-@Exp@ constraint reads out here).
    ComparisonThetaConflict PropId LeafId LeafId Param Term Term
  | -- | the named leaves do not expose any recheck parameter at one of the
    -- authored system/measurand/dataset terms.
    ComparisonRecheckRoleMissing PropId RuleId String
  | -- | a named leaf reports a measurand other than the one after @on@.
    ComparisonMeasurandInconsistent PropId LeafId MeasurandId Term
  | -- | θ left one of the scheme's rule parameters unbound.
    ComparisonUnboundParam PropId RuleId Param
  | -- | the certificate's @(prem i)@ slots cannot be attributed to the named
    -- leaves from the @recheck@ rule's conclusion pattern.
    ComparisonCertSlotUndeterminable PropId RuleId
  | -- | a generated @recheck@\/@bridge@\/@claims@ id collides with a declared
    -- declaration or with another block's: the offending id.
    ComparisonIdCollision PropId String
  | -- | two @comparison@ blocks state the same comparison: this block's
    -- sub-claim id and the earlier block's.
    ComparisonDuplicateBlock PropId PropId
  deriving (Eq, Show)

-- | Render an 'ElabError' as a single human-readable line.
--
-- Human-facing premise indices are 1-based ('UnresolvedPremise',
-- 'AmbiguousPremise' — @resolvePremises@ zips @[1..]@); every /machine/ index
-- (a resolved 'Step', a generated @(prem i)@ slot) is 0-based, and the two are
-- converted only here, at the message boundary (plan §5, eng review 6A). The
-- slot-valued comparison errors below report the 0-based slot as such, saying
-- so explicitly, because they name a certificate position the author can read
-- back out of the generated argument.
elabErrorMessage :: ElabError -> String
elabErrorMessage e = case e of
  PolicyIdMismatch (PolicyId p) (PolicyId q) ->
    "program declares policy '" ++ p ++ "' but the supplied policy is '" ++ q ++ "'"
  UnknownRule (ArgId a) (RuleId r) ->
    "arg '" ++ a ++ "': unknown rule '" ++ r ++ "' (not declared in the policy)"
  ThetaReferenceCountMismatch (ArgId a) (RuleId r) expected got ->
    "arg '" ++ a ++ "': rule '" ++ r ++ "' inference expects "
      ++ show expected ++ " reference(s) but " ++ show got ++ " were supplied"
  ThetaReferenceUnresolved (ArgId a) (RuleId r) i (ArgRef ref) ->
    "arg '" ++ a ++ "': rule '" ++ r ++ "' inference premise #" ++ show i
      ++ " reference '" ++ ref
      ++ "' names neither a declared leaf nor prior argument"
  ThetaReferenceAmbiguous (ArgId a) (RuleId r) i (ArgRef ref) ->
    "arg '" ++ a ++ "': rule '" ++ r ++ "' inference premise #" ++ show i
      ++ " reference '" ++ ref
      ++ "' is ambiguous between a declared leaf and a prior argument"
  ThetaReferenceShapeMismatch (ArgId a) (RuleId r) i (ArgRef ref) p ->
    "arg '" ++ a ++ "': rule '" ++ r ++ "' inference premise #" ++ show i
      ++ " reference '" ++ ref ++ "' selected proposition " ++ prettyProp p
      ++ " but it does not match the premise pattern"
  ThetaReferenceConflict (ArgId a) (RuleId r) i (ArgRef ref) (Param x) old new ->
    "arg '" ++ a ++ "': rule '" ++ r ++ "' inference premise #" ++ show i
      ++ " reference '" ++ ref ++ "' binds parameter '" ++ x
      ++ "' inconsistently: " ++ prettyTerm old ++ " vs " ++ prettyTerm new
  ThetaReferenceConclUnderivable (ArgId a) (RuleId r) i (ArgRef ref) ->
    "arg '" ++ a ++ "': rule '" ++ r ++ "' inference premise #" ++ show i
      ++ " reference '" ++ ref
      ++ "' resolves to a prior argument whose conclusion is underivable"
  ThetaParameterUnbound (ArgId a) (RuleId r) (Param x) ->
    "arg '" ++ a ++ "': rule '" ++ r ++ "' parameter '" ++ x
      ++ "' is not bound by inferred theta"
  CertSlotUnresolved a b v n (RuleId r) ->
    certSlotPrefix a b v n ++ "names neither a premise label of rule '" ++ r
      ++ "', a declared leaf, nor a prior argument"
  CertSlotAmbiguous a b v n ->
    certSlotPrefix a b v n ++ "is ambiguous between a declared leaf and a prior argument"
  CertSlotLabelAmbiguous a b v n (RuleId r) ->
    certSlotPrefix a b v n ++ "is ambiguous between rule '" ++ r
      ++ "' premise label and a declared leaf or prior argument"
  CertSlotNotAPremise a b v n ->
    certSlotPrefix a b v n ++ "does not resolve to any of this argument's premise slots"
  CertSlotMultiSlot a b v n i j allMatchesLabelled ->
    certSlotPrefix a b v n ++ "occupies premise slots " ++ show i ++ " and " ++ show j
      ++ "; cite a numeric slot"
      ++ if allMatchesLabelled
        then " or the rule's premise label for the slot you mean"
        else ""
  CertSlotNonCanonicalNumeral a b v n ->
    certSlotPrefix a b v n ++ "is not a canonical slot numeral "
      ++ "(use unsigned decimal with no leading zeros); write the canonical numeral or a source name"
  CertSlotSchemaMismatch (ArgId a) b v (ArgRef n) ->
    "arg '" ++ a ++ "': certificate '" ++ certBackendSpelling b v
      ++ "' payload does not match the backend's premise-reference schema but "
      ++ "contains symbolic premise reference '" ++ n ++ "'"
  CertNdBinderUnbound a b v n ->
    certNdPrefix a b v ++ "reference '" ++ argRefText n ++ "' names no enclosing lam binder"
  CertNdBinderShadowed a b v n ->
    certNdPrefix a b v ++ "lam binder '" ++ argRefText n ++ "' shadows an enclosing binder; rename one"
  CertNdBinderShadowsPremise a b v n ->
    certNdPrefix a b v ++ "lam binder '" ++ argRefText n ++ "' is also a citable premise name of this instance; rename the binder"
  CertNdMalformedBinder a b v n ->
    certNdPrefix a b v ++ "lam binder '" ++ argRefText n ++ "' is not a source identifier"
  CertNdNonCanonicalIndex a b v n ->
    certNdPrefix a b v ++ "index '" ++ argRefText n ++ "' is not a canonical index (use unsigned decimal with no leading zeros)"
  CertNdKernelIndex a b v n ->
    certNdPrefix a b v ++ "kernel index '" ++ argRefText n ++ "' appears in a named-form payload; cite a binder by name, a premise with (prem ...), or a theory entry with (thy ...)"
  CertNdPremOutOfRange a b v n i j ->
    certNdPrefix a b v ++ "premise reference '" ++ argRefText n ++ "' names slot " ++ show i
      ++ " but this argument has only " ++ show j ++ " premise slot(s)"
  CertNdFormulaMalformed a b v n ->
    certNdPrefix a b v ++ "formula annotation '" ++ argRefText n ++ "' is not a source proposition"
  CertNdResidualNamed a b v n ->
    certNdPrefix a b v ++ "named spelling '" ++ argRefText n ++ "' sits where the nd@1 grammar gives it no meaning"
  ArityMismatch (ArgId a) (RuleId r) expd got ->
    "arg '" ++ a ++ "': rule '" ++ r ++ "' expects " ++ show expd
      ++ " argument(s) but " ++ show got ++ " were supplied"
  UnresolvedPremise (ArgId a) (RuleId r) i g ->
    "arg '" ++ a ++ "': rule '" ++ r ++ "' premise #" ++ show i
      ++ " (" ++ prettyProp g ++ ") matches no declared leaf or prior argument"
  AmbiguousPremise (ArgId a) (RuleId r) i g ms ->
    "arg '" ++ a ++ "': rule '" ++ r ++ "' premise #" ++ show i
      ++ " (" ++ prettyProp g ++ ") is ambiguous — matched " ++ show ms
  UnresolvedDischarge (ArgId a) (QuestionId q) (ArgRef ref) ->
    "arg '" ++ a ++ "': discharge of '" ++ q ++ "' names '" ++ ref
      ++ "', which is neither a declared leaf nor a prior argument"
  AmbiguousDischarge (ArgId a) (QuestionId q) (ArgRef ref) ->
    "arg '" ++ a ++ "': discharge of '" ++ q ++ "' names '" ++ ref
      ++ "', which is ambiguous between a declared leaf and a prior argument"
  ConclusionMismatch (ArgId a) (PropId c) w formal ->
    "arg '" ++ a ++ "': supports(" ++ c ++ ") but its conclusion "
      ++ prettyProp w ++ " ≢ the claim formal " ++ prettyProp formal
  UnknownStatusClaim (PropId c) ->
    "status '" ++ c ++ "': not a declared claim"
  ChallengeTargetUndeclared (ArgId a) ->
    "arg '" ++ a ++ "': challenges(…) target is not a declared argument or leaf"
  DuplicateArgId (ArgId a) ->
    "arg '" ++ a ++ "': duplicate argument id"
  AttackEndpointUndeclared (ArgId a) ->
    "attack endpoint is not a declared argument: " ++ show a
  DuplicateGroupId (GroupId g) ->
    "group '" ++ g ++ "': duplicate group id"
  GroupRepeatedMember (GroupId g) (LeafId l) ->
    "group '" ++ g ++ "': repeats member '" ++ l ++ "'"
  GroupTooFewMembers (GroupId g) ->
    "group '" ++ g ++ "': fewer than two members (cannot report a conflict)"
  GroupMemberUndeclared (GroupId g) (LeafId l) ->
    "group '" ++ g ++ "': member '" ++ l ++ "' is not a declared leaf"
  PremiseLabelCountMismatch r labels premises ->
    rulePrefix r ++ "has " ++ show labels ++ " premise-label entries for "
      ++ show premises ++ " premises"
  PremiseLabelDuplicate r l ->
    rulePrefix r ++ "duplicate premise label '" ++ labelText l ++ "'"
  PremiseLabelReserved r l ->
    rulePrefix r ++ "premise label '" ++ labelText l
      ++ "' is reserved (the §7 terminal markers 'rule' and 'leaf')"
  PremiseLabelQuestionCollision r l ->
    rulePrefix r ++ "premise label '" ++ labelText l
      ++ "' also names a critical question of the same rule"
  AttackStepUnresolved (ArgId w) (ArgId u) seg ->
    "attack from '" ++ w ++ "' on '" ++ u ++ "': path segment '" ++ seg
      ++ "' names neither a premise label nor a critical question of the targeted rule"
  DuplicateValueBinding (ValueName n) ->
    valuePrefix n ++ "duplicate declaration"
  ReservedValueName (ValueName n) ->
    valuePrefix n ++ "reserved name (the 'cell' interpolation head)"
  ValueNameConstructorCollision (ValueName n) ->
    valuePrefix n ++ "collides with declared constructor '" ++ n ++ "'"
  ValueBindingSortError (ValueName n) fault ->
    valuePrefix n ++ "ill-sorted right-hand side: " ++ sortFaultText fault
  ValueBindingClaimSortError (PropId c) fault ->
    "claim '" ++ c ++ "': ill-sorted formal after value substitution: "
      ++ sortFaultText fault
  NlValueBindingMissing (PropId c) (ValueName n) ->
    "claim '" ++ c ++ "': nl references undeclared value '" ++ n ++ "'"
  NlUnterminatedBrace c ->
    nlPrefix c ++ "has an unterminated '{' directive"
  NlStrayBrace c ->
    nlPrefix c ++ "has an unescaped '}' (write '}}' for a literal brace)"
  NlUnknownDirective c body ->
    nlPrefix c ++ "has an unknown directive '{" ++ body
      ++ "}' (expected '{<value>}' or '{cell <leaf>}')"
  NlCellLeafUndeclared c (LeafId l) ->
    nlPrefix c ++ "directive '{cell " ++ l ++ "}' names '" ++ l
      ++ "', which is not a declared leaf"
  NlCellObligation c (LeafId l) ->
    nlPrefix c ++ "directive '{cell " ++ l ++ "}' names a leaf that does not carry "
      ++ "exactly one numeric literal (the premise-cell obligation)"
  ComparisonUndeclaredMeasurand c (MeasurandId m) ->
    cmpPrefix c ++ "measurand '" ++ m ++ "' is not declared by the policy"
  ComparisonMeasurandNoPolarity c (MeasurandId m) ->
    cmpPrefix c ++ "measurand '" ++ m ++ "' declares no polarity, so it cannot "
      ++ "key a comparison-scheme (a polarity clause is well-formed only on a "
      ++ "Num-sorted measurand)"
  ComparisonNoScheme c rel pol ->
    cmpPrefix c ++ "the policy declares no comparison-scheme for ("
      ++ relationStr rel ++ ", " ++ polarityStr pol ++ ")"
  ComparisonSchemeRuleUnknown c (RuleId r) ->
    cmpPrefix c ++ "the comparison-scheme names rule '" ++ r
      ++ "', which the policy does not declare"
  ComparisonRecheckNotStrict c (RuleId r) ->
    cmpPrefix c ++ "the scheme's recheck rule '" ++ r ++ "' is not strict"
  ComparisonRecheckCertifierMissing c (RuleId r) ->
    cmpPrefix c ++ "the scheme's recheck rule '" ++ r ++ "' lists no ord@1 certifier"
  ComparisonBridgeNotDefeasible c (RuleId r) ->
    cmpPrefix c ++ "the scheme's bridge rule '" ++ r ++ "' is not defeasible"
  ComparisonBridgeConclusionShape c (RuleId r) ->
    cmpPrefix c ++ "the scheme's bridge rule '" ++ r
      ++ "' does not conclude a 4-ary atom over four distinct parameters "
      ++ "(the favored system first)"
  ComparisonBridgePremiseShape c (RuleId r) ->
    cmpPrefix c ++ "the scheme's bridge rule '" ++ r
      ++ "' must have exactly one premise admitting the generated comparison "
      ++ "and one premise admitting the named binding leaf"
  ComparisonRecheckConclusionShape c (RuleId r) ->
    cmpPrefix c ++ "the scheme's recheck rule '" ++ r
      ++ "' does not conclude a 2-ary comparison atom"
  ComparisonSchemeDirectionMismatch c (RuleId r) pol ->
    cmpPrefix c ++ "the scheme's recheck rule '" ++ r
      ++ "' concludes in the wrong direction for a " ++ polarityStr pol
      ++ " measurand: its conclusion must name " ++ directionWording pol
      ++ ", but it names them the other way round"
  ComparisonConclusionShape c p ->
    cmpPrefix c ++ "the authored conclusion " ++ prettyProp p
      ++ " is not a 2-ary system pair"
  ComparisonConclusionPredMismatch c (RuleId r) (Pred authored) (Pred declared) ->
    cmpPrefix c ++ "the authored conclusion '" ++ authored
      ++ "' does not match the bridge rule '" ++ r ++ "' conclusion pattern '"
      ++ declared ++ "'"
  ComparisonLeafUndeclared c (LeafId l) ->
    cmpPrefix c ++ "'" ++ l ++ "' is not a declared leaf"
  ComparisonBindingNotLeaf c (LeafId l) ->
    cmpPrefix c ++ "binding = '" ++ l ++ "' is not a declared leaf"
  ComparisonBindingNotAdmitted c (LeafId l) (RuleId r) ->
    cmpPrefix c ++ "binding = '" ++ l
      ++ "' is not admitted by the selected bridge rule '" ++ r ++ "'"
  ComparisonSameLeaf c (LeafId l) ->
    cmpPrefix c ++ "result and baseline name the same leaf '" ++ l ++ "'"
  ComparisonCellObligation c (LeafId l) ->
    cmpPrefix c ++ "leaf '" ++ l ++ "' does not carry exactly one numeric literal "
      ++ "(the premise-cell obligation)"
  ComparisonNoPremiseSlot c (RuleId r) (LeafId l) ->
    cmpPrefix c ++ "leaf '" ++ l ++ "' matches no premise pattern of the recheck rule '"
      ++ r ++ "'"
  ComparisonAmbiguousPremiseSlot c (RuleId r) (LeafId l) slots ->
    cmpPrefix c ++ "leaf '" ++ l ++ "' matches premise slots " ++ show slots
      ++ " (0-based) of the recheck rule '" ++ r ++ "'"
  ComparisonSlotClash c (RuleId r) i ->
    cmpPrefix c ++ "result and baseline both resolve to premise slot " ++ show i
      ++ " (0-based) of the recheck rule '" ++ r ++ "'"
  ComparisonThetaConflict c (LeafId b) (LeafId r) (Param x) old new ->
    cmpPrefix c ++ "leaves '" ++ b ++ "' and '" ++ r ++ "' bind '" ++ x
      ++ "' inconsistently: " ++ prettyTerm old ++ " vs " ++ prettyTerm new
  ComparisonMeasurandInconsistent c (LeafId l) (MeasurandId m) t ->
    cmpPrefix c ++ "leaf '" ++ l ++ "' reports measurand " ++ prettyTerm t
      ++ " but the block says on " ++ m
  ComparisonUnboundParam c (RuleId r) (Param x) ->
    cmpPrefix c ++ "rule '" ++ r ++ "' parameter '" ++ x
      ++ "' is not bound by the derived θ"
  ComparisonRecheckRoleMissing c (RuleId r) role ->
    cmpPrefix c ++ "cannot identify the recheck rule '" ++ r ++ "' parameter "
      ++ "for the comparison's " ++ role
  ComparisonCertSlotUndeterminable c (RuleId r) ->
    cmpPrefix c ++ "cannot attribute the certificate's premise slots to the named "
      ++ "leaves from the recheck rule '" ++ r ++ "' conclusion pattern"
  ComparisonIdCollision c name ->
    cmpPrefix c ++ "generated id '" ++ name ++ "' collides with another declaration"
  ComparisonDuplicateBlock c (PropId other) ->
    cmpPrefix c ++ "duplicates the comparison claiming '" ++ other ++ "'"

-- | Location prefix for a certificate premise reference (#105): the citing
-- @arg@, the certificate's @beta\@version@, and the reference as written.
-- 'CertSlotSchemaMismatch' is the one member of the family that does not use
-- it — that failure is about the payload, and only mentions the reference to
-- say why the payload could not be passed through.
certSlotPrefix :: ArgId -> BackendId -> Int -> ArgRef -> String
certSlotPrefix (ArgId a) backend version (ArgRef name) =
  "arg '" ++ a ++ "': certificate '" ++ certBackendSpelling backend version
    ++ "' premise reference '" ++ name ++ "' "

certNdPrefix :: ArgId -> BackendId -> Int -> String
certNdPrefix (ArgId a) backend version =
  "arg '" ++ a ++ "': certificate '" ++ certBackendSpelling backend version ++ "' "

argRefText :: ArgRef -> String
argRefText (ArgRef name) = name

certBackendSpelling :: BackendId -> Int -> String
certBackendSpelling (BackendId backend) version = backend ++ "@" ++ show version

-- | Location prefix for a @comparison@ block, named by the sub-claim it
-- declares (App. B.3's @claims@ id — the one id every block must carry).
cmpPrefix :: PropId -> String
cmpPrefix (PropId c) = "comparison claiming '" ++ c ++ "': "

-- | The operand order a recheck conclusion must carry to realize a polarity
-- (App. B.2). The same table 'Lara.Elaborate.Comparison' checks against, worded
-- for an author: "result" and "baseline" are the two @comparison@ fields, not
-- rule parameters, because the parameter names are the policy author's choice.
directionWording :: Polarity -> String
directionWording pol = case pol of
  HigherIsBetter -> "the baseline cell first and the result cell second"
  LowerIsBetter -> "the result cell first and the baseline cell second"

-- | Location prefix for an @nl@ interpolation failure (App. B.6, extended by
-- App. C.5).
nlPrefix :: PropId -> String
nlPrefix (PropId c) = "claim '" ++ c ++ "': nl "

valuePrefix :: String -> String
valuePrefix n = "value binding '" ++ n ++ "': "

sortFaultText :: SortFault -> String
sortFaultText fault = case fault of
  FaultUndeclaredPred (Pred p) ->
    "undeclared predicate '" ++ p ++ "'"
  FaultUndeclaredCon (FunSym k) ->
    "undeclared constructor '" ++ k ++ "'"
  FaultPredArity (Pred p) expected actual ->
    "predicate '" ++ p ++ "' expects " ++ show expected
      ++ " argument(s) but got " ++ show actual
  FaultConArity (FunSym k) expected actual ->
    "constructor '" ++ k ++ "' expects " ++ show expected
      ++ " argument(s) but got " ++ show actual
  FaultArgSort expected actual ->
    "expected sort " ++ sortText expected ++ " but got " ++ sortText actual

-- | Location prefix for a policy well-formedness failure on a rule.
rulePrefix :: RuleId -> String
rulePrefix (RuleId r) = "rule '" ++ r ++ "': "

labelText :: PremiseLabel -> String
labelText (PremiseLabel l) = l
