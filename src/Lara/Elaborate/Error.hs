-- | The elaborator's located-ish failure type and its renderer.
--
-- Split out of "Lara.Elaborate.Internal" so the @lara-syntax\@0.3@ surface
-- expansion ("Lara.Elaborate.Comparison") and the structural lowering can both
-- raise the same errors without an import cycle. 'Lara.Elaborate.Internal'
-- re-exports both names, so every existing importer is unaffected.
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

-- | A located-ish elaboration failure. Each constructor names the offending
-- argument, rule, leaf, claim, comparison, or position so the caller can render
-- a diagnostic (see 'elabErrorMessage'). The elaborator is deterministic, so
-- the /first/ error in declaration order is the one reported.
data ElabError
  = -- | @programPolicy prog@ ≠ @policyId policy@ (the header-match invariant).
    PolicyIdMismatch PolicyId PolicyId
  | -- | a @by r(…)@ names a rule absent from the policy: @arg@, @rule@.
    UnknownRule ArgId RuleId
  | -- | positional θ length ≠ the rule's parameter count: @arg@, @rule@,
    -- expected, got.
    ArityMismatch ArgId RuleId Int Int
  | -- | no declared leaf\/prior-arg conclusion @≡@ the ground premise: @arg@,
    -- @rule@, 1-based premise index, the ground premise proposition.
    UnresolvedPremise ArgId RuleId Int Prop
  | -- | ≥2 declared conclusions @≡@ the ground premise: @arg@, @rule@, premise
    -- index, the ground premise, and the matching leaf\/arg ids.
    AmbiguousPremise ArgId RuleId Int Prop [String]
  | -- | a @discharge q with ref@ whose @ref@ is neither a declared leaf nor a
    -- prior arg: @arg@, @question@, the ref name.
    UnresolvedDischarge ArgId QuestionId String
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
  ArityMismatch (ArgId a) (RuleId r) expd got ->
    "arg '" ++ a ++ "': rule '" ++ r ++ "' expects " ++ show expd
      ++ " argument(s) but " ++ show got ++ " were supplied"
  UnresolvedPremise (ArgId a) (RuleId r) i g ->
    "arg '" ++ a ++ "': rule '" ++ r ++ "' premise #" ++ show i
      ++ " (" ++ prettyProp g ++ ") matches no declared leaf or prior argument"
  AmbiguousPremise (ArgId a) (RuleId r) i g ms ->
    "arg '" ++ a ++ "': rule '" ++ r ++ "' premise #" ++ show i
      ++ " (" ++ prettyProp g ++ ") is ambiguous — matched " ++ show ms
  UnresolvedDischarge (ArgId a) (QuestionId q) ref ->
    "arg '" ++ a ++ "': discharge of '" ++ q ++ "' names '" ++ ref
      ++ "', which is neither a declared leaf nor a prior argument"
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
  NlUnterminatedBrace c ->
    nlPrefix c ++ "has an unterminated '{' directive"
  NlStrayBrace c ->
    nlPrefix c ++ "has an unescaped '}' (write '}}' for a literal brace)"
  NlUnknownDirective c body ->
    nlPrefix c ++ "has an unknown directive '{" ++ body ++ "}' (expected '{cell <leaf>}')"
  NlCellLeafUndeclared c (LeafId l) ->
    nlPrefix c ++ "directive '{cell " ++ l ++ "}' names '" ++ l
      ++ "', which is not a declared leaf"
  NlCellObligation c (LeafId l) ->
    nlPrefix c ++ "directive '{cell " ++ l ++ "}' names a leaf that does not carry "
      ++ "exactly one numeric literal (the premise-cell obligation)"
  ComparisonUndeclaredMeasurand c (MeasurandId m) ->
    cmpPrefix c ++ "measurand '" ++ m ++ "' is not declared by the policy"
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

-- | Location prefix for an @nl@ interpolation failure (App. B.6).
nlPrefix :: PropId -> String
nlPrefix (PropId c) = "claim '" ++ c ++ "': nl "

-- | Location prefix for a policy well-formedness failure on a rule.
rulePrefix :: RuleId -> String
rulePrefix (RuleId r) = "rule '" ++ r ++ "': "

labelText :: PremiseLabel -> String
labelText (PremiseLabel l) = l
