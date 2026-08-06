-- | Abstract syntax of the LARA claim-support language (spec §2–§8).
--
-- == Status: placeholder types, no checker yet
--
-- This module declares the /shape/ of a LARA program — the data the checker
-- will eventually consume — but implements __no checking__. It is the datatype
-- skeleton for spec Sections 2–8: names, leaves, claims, policy rules, support
-- terms, positional attacks, and the top-level program. Every constructor is a
-- direct transcription of a spec production; the judgments
-- (@Σ; Π; Γ; R ⊢ w : supports(p) ▷ O@, attack well-formedness, compilation to a
-- Dung framework, grounded labelling) are deliberately absent and will land in
-- later modules (@Lara.Check@, @Lara.Compile@, @Lara.Grounded@).
--
-- Propositions and the trusted identity relation @≡@ already exist in
-- "Lara.Prop"; this module reuses them rather than redefining atoms. The LP
-- pieces in "Lara.Term" / "Lara.Formula" / "Lara.Kernel" are a separate,
-- optional /strict backend adapter/ seed (spec §5.2) and are intentionally not
-- referenced here: a backend certificate is an __opaque payload__ ('Cert') at
-- this layer.
--
-- The one abstract syntax has two front ends (spec §1): the presentation syntax
-- used in the paper and the JSON wire encoding. Both decode to the types below.
module Lara.AST
  ( -- * Names (spec §2)
    PropId (..)
  , QuestionId (..)
  , LeafId (..)
  , RuleId (..)
  , ArgId (..)
  , ObligationId (..)
  , BackendId (..)
  , PolicyId (..)
  , Param (..)
    -- * Leaves (spec §3)
  , LeafKind (..)
  , Provenance (..)
  , SourceRef (..)
  , Leaf (..)
  , GroupId (..)
  , DupGroup (..)
  , GroupConflictMode (..)
    -- * Claims (spec §3.1)
  , AuditStatus (..)
  , Binding (..)
  , Claim (..)
    -- * Policy: rules, patterns, obligations (spec §4)
  , Mode (..)
  , Pred (..)
  , FunSym (..)
  , Pat (..)
  , AtomPat (..)
  , Necessity (..)
  , Question (..)
  , Assurance'
  , CertRef (..)
  , Rule (..)
  , Contrary (..)
  , Exception (..)
  , Admission (..)
  , Policy (..)
    -- * Backends (spec §5)
  , TheoryDigest (..)
  , Cert (..)
  , Assurance (..)
    -- * Support terms (spec §6)
  , Subst
  , SupportTerm (..)
    -- * Positional attacks (spec §7)
  , Step (..)
  , Position
  , Attack (..)
    -- * Programs (spec §2, §4.4)
  , Digest (..)
  , ChallengeTarget (..)
  , ArgConcl (..)
  , Arg (..)
  , Decl (..)
  , Program (..)
    -- * Checker-boundary units (the M3 wire anchor)
  , Unit (..)
    -- * Claim status (spec §8)
  , Status (..)
  , Label (..)
    -- * Rejection outcomes (spec §10.1)
  , RejectClass (..)
  , Rejection (..)
  ) where

import Lara.Prop (FunSym (..), Pred (..), Prop, Term)
import Lara.Strict (SExpr)

-- ---------------------------------------------------------------------------
-- Names (spec §2)
-- ---------------------------------------------------------------------------
--
-- Each identifier class is its own newtype so the type checker keeps them
-- apart; the spec's metavariables (@p@, @q@, @l@, @r@, @beta@, …) map one-to-one.

-- | Proposition and claim identifier (@p@). Propositions themselves are
-- "Lara.Prop" values; a 'PropId' names a declared claim root.
newtype PropId = PropId String deriving (Eq, Ord, Show)

-- | Critical-question identifier (@q@).
newtype QuestionId = QuestionId String deriving (Eq, Ord, Show)

-- | Evidence-leaf identifier (@l@).
newtype LeafId = LeafId String deriving (Eq, Ord, Show)

-- | Inference-scheme (rule) identifier (@r@).
newtype RuleId = RuleId String deriving (Eq, Ord, Show)

-- | Support-term / argument identifier (@a@, @w@, @u@).
newtype ArgId = ArgId String deriving (Eq, Ord, Show)

-- | Obligation identifier (@o@).
newtype ObligationId = ObligationId String deriving (Eq, Ord, Show)

-- | Strict-certificate backend identifier (@beta@), e.g. @nd@ or @lp@.
newtype BackendId = BackendId String deriving (Eq, Ord, Show)

-- | Versioned claim-support-policy identifier (@policy@ / @Pi@).
newtype PolicyId = PolicyId String deriving (Eq, Ord, Show)

-- | A rule parameter (@X@) ranging over ground terms in an instance.
newtype Param = Param String deriving (Eq, Ord, Show)

-- ---------------------------------------------------------------------------
-- Leaves (spec §3)
-- ---------------------------------------------------------------------------

-- | How an evidence leaf entered the artifact (spec §3).
data LeafKind = Observed | Attested | Assumed | Certified
  deriving (Eq, Ord, Show)

-- | Who produced a leaf or a lowering step (spec §3, §11). The checker record
-- for @certified@ leaves is @Checker name version@.
data Provenance
  = User
  | AiExecuted
  | Checker String String -- ^ @checker(name, version)@
  deriving (Eq, Ord, Show)

-- | An artifact source reference (@src@): a pointer into the snapshot, e.g.
-- @evidence/table_2.csv#row=mean@.
newtype SourceRef = SourceRef String deriving (Eq, Ord, Show)

-- | A declared evidence leaf (spec §3).
--
-- > leaf l : prop
-- >   kind       = leaf-kind
-- >   provenance = provenance
-- >   refs       = [src*]
data Leaf = Leaf
  { leafId :: LeafId
  , leafProp :: Prop
  , leafKind :: LeafKind
  , leafProvenance :: Provenance
  , leafRefs :: [SourceRef]
  }
  deriving (Eq, Show)

-- | Duplicate-report-group identifier (@g@), named so an R9 data-integrity
-- diagnostic can locate the group declaration (spec §4.3, §10.1).
newtype GroupId = GroupId String deriving (Eq, Ord, Show)

-- | A declared duplicate-report group (spec §4.3, M0 C16): one measurand cell
-- reported more than once, each report a distinct leaf, declared as a group so
-- the checker can enforce agreement within it by the frozen @≡@ relation. The
-- declaration is untrusted elaborator output; measurand identity never enters
-- the trusted kernel.
--
-- > group g = [ l1, l2, ... ]
data DupGroup = DupGroup
  { dgId :: GroupId
  , dgMembers :: [LeafId]
  }
  deriving (Eq, Ord, Show)

-- | Policy outcome for a duplicate-report group whose members are not pairwise
-- @≡@ (spec §4.3). The default keeps one corrupted cell from rendering the rest
-- of the artifact uncheckable; a policy may escalate to a whole-program error.
--
-- * @QuarantineOnConflict@ (default): every argument whose support term uses a
--   conflicted member is dropped from the checked program (and the members leave
--   the context @Γ@), so the dependent claim loses that support and routes to
--   @gap@ — never a rejection. (The argument is dropped at the driver boundary,
--   __not__ by letting a leaf occurrence fail the §6.1 leaf rule; that would be
--   an R1 whole-program rejection, not @gap@ — see "Lara.Driver".'Lara.Driver.quarantineUnit'.)
-- * @RejectOnConflict@: a detected conflict is a whole-program data-integrity
--   error (rejection class R9), located at the group declaration.
data GroupConflictMode = QuarantineOnConflict | RejectOnConflict
  deriving (Eq, Ord, Show)

-- ---------------------------------------------------------------------------
-- Claims (spec §3.1)
-- ---------------------------------------------------------------------------

-- | The (untrusted, human-signed) audit state of a claim binding (spec §3.1).
data AuditStatus = Unreviewed | Reviewed | Disputed
  deriving (Eq, Ord, Show)

-- | The untrusted binding between a claim's natural-language text and its
-- formal target (spec §3.1). Never a checker obligation; evaluated on the
-- semantic-faithfulness axis, not proved.
data Binding = Binding
  { bindingAuthor :: String
  , bindingRationale :: String
  , bindingAuditStatus :: AuditStatus
  }
  deriving (Eq, Show)

-- | A claim: a natural-language string, a formal target proposition, and the
-- untrusted binding between them (spec §3.1).
--
-- @w supports c@ holds iff @concl(w) ≡ c.claimFormal@ under "Lara.Prop"'s @≡@.
data Claim = Claim
  { claimId :: PropId
  , claimNl :: String
  , claimFormal :: Prop
  , claimBinding :: Binding
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Policy: rules, patterns, obligations (spec §4)
-- ---------------------------------------------------------------------------

-- | A rule's mode (spec §4). Strict rules are deductive and unattackable;
-- defeasible rules give presumptive support and carry critical questions.
data Mode = Strict | Defeasible
  deriving (Eq, Ord, Show)

-- | A pattern term over a rule's parameters (spec §4.1): @P ::= X | k | k(P…)@.
data Pat
  = PVar Param
  | PLit Term -- ^ a ground literal used verbatim in the pattern
  | PCon FunSym [Pat] -- ^ constructor applied to sub-patterns
  deriving (Eq, Show)

-- | An atom pattern (spec §4.1): @Apat ::= pred(P1, …, Pn)@. Reuses "Lara.Prop"'s
-- 'Pred'\/'FunSym' so a pattern head cannot be confused with a term head.
data AtomPat = AtomPat Pred [Pat]
  deriving (Eq, Show)

-- | Whether an open critical question produces an obligation (spec §4.2). A
-- @mandatory@ hole excludes the argument from the AF; @optional@ is a diagnostic.
data Necessity = Mandatory | Optional
  deriving (Eq, Ord, Show)

-- | A rule's critical question (spec §4.2): an answer pattern plus its necessity.
data Question = Question
  { questionId :: QuestionId
  , questionAnswer :: AtomPat
  , questionNecessity :: Necessity
  }
  deriving (Eq, Show)

-- | Reference to a certifier a strict rule accepts (spec §4): a versioned
-- backend paired with the theory digest it is allowed to use.
data CertRef = CertRef
  { certRefBackend :: BackendId
  , certRefVersion :: Int -- ^ backend version (a wire NAT)
  , certRefTheory :: TheoryDigest
  }
  deriving (Eq, Show)

-- | A named inference scheme (spec §4).
--
-- > rule r(X1, …, Xm)
-- >   mode       = strict | defeasible
-- >   premises   = [Apat*]
-- >   conclusion = Apat
-- >   allow-trusted = ...        -- strict rules only
-- >   certifiers    = [...]      -- strict rules only
-- >   question q : Apat (mandatory | optional)*
--
-- Well-formedness (spec §4.1) — every variable in premises/conclusion/answers/
-- exceptions is among 'ruleParams', symbol arities match @Sigma@ — is a checker
-- obligation, not enforced by the datatype.
data Rule = Rule
  { ruleId :: RuleId
  , ruleParams :: [Param]
  , ruleMode :: Mode
  , rulePremises :: [AtomPat]
  , ruleConclusion :: AtomPat
  , ruleAllowTrusted :: Bool -- ^ strict only; @False@ for defeasible
  , ruleCertifiers :: [CertRef] -- ^ strict only; @[]@ for defeasible
  , ruleQuestions :: [Question]
  }
  deriving (Eq, Show)

-- | A policy-declared conflict, closed under ground instantiation (spec §4.1).
-- The only source of propositional conflict; rebut/undermine check against it.
data Contrary = Contrary AtomPat AtomPat
  deriving (Eq, Show)

-- | A policy-declared undercutting condition for a rule (spec §4.2): licenses an
-- undercut of exactly those instances of 'exceptionRule' whose @theta@ makes
-- 'exceptionAtom' the attacker's conclusion.
data Exception = Exception
  { exceptionRule :: RuleId
  , exceptionAtom :: AtomPat
  }
  deriving (Eq, Show)

-- | The leaf-admission outcome for a @(kind, provenance)@ pair (spec §4.3).
data Admission = Admit | Quarantine | Reject
  deriving (Eq, Ord, Show)

-- | A versioned claim-support policy (spec §4): the trusted input a program
-- instantiates but may not modify. The admission map is a total function over
-- @kind × provenance@; here it is given as an association list placeholder.
data Policy = Policy
  { policyId :: PolicyId
  , policyRules :: [Rule]
  , policyContraries :: [Contrary]
  , policyExceptions :: [Exception]
  , policyAdmission :: [((LeafKind, Provenance), Admission)]
  , policyTheories :: [(TheoryDigest, [Prop])]
    -- ^ Trusted theory table (lara-syntax@0.2, grammar App. A.2); lowered to
    -- 'unitTheories' via the elaborator's 'TheoryRegistry'.
  , policyGroupMode :: GroupConflictMode
    -- ^ How a duplicate-report group with @≢@ members is handled (spec §4.3):
    -- 'QuarantineOnConflict' (default) or 'RejectOnConflict' (R9). Lowered to
    -- 'unitGroupMode'.
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Backends (spec §5)
-- ---------------------------------------------------------------------------

-- | A digest addressing a fixed backend theory (spec §5). Part of replay
-- identity.
newtype TheoryDigest = TheoryDigest String deriving (Eq, Ord, Show)

-- | An __opaque__ strict-certificate payload (spec §5). The source calculus is
-- independent of every backend's formulas and proof terms, so at this layer a
-- certificate is the frozen triple @(beta, theory-digest, kappa)@ — a versioned
-- backend, a digest-addressed theory, and the opaque certificate as an
-- 'SExpr' wire value (the N11 anchor; only the named backend decodes it). The
-- natural-deduction reference adapter (spec §5.1) and the optional LP adapter
-- (spec §5.2, "Lara.Kernel") decode and check it; this type never inspects it.
data Cert = Cert
  { certBackend :: BackendId
  , certVersion :: Int -- ^ backend version (a wire NAT)
  , certTheory :: TheoryDigest
  , certPayload :: SExpr -- ^ opaque, backend-decoded (kappa)
  }
  deriving (Eq, Show)

-- | The assurance carried by a support-term rule instance (spec §6).
--
-- A defeasible instance is 'AssuranceNone'. A strict instance is either
-- 'AssuranceTrusted' (only when the rule's @allow-trusted@) or
-- 'AssuranceCert' (an opaque backend certificate, spec §5).
data Assurance
  = AssuranceNone
  | AssuranceTrusted
  | AssuranceCert Cert
  deriving (Eq, Show)

-- | Alias kept for the spec's @assurance@ metavariable at call sites.
type Assurance' = Assurance

-- ---------------------------------------------------------------------------
-- Support terms (spec §6)
-- ---------------------------------------------------------------------------

-- | A ground substitution @theta@ mapping each instantiated rule parameter to a
-- ground term (spec §4.1). Instances are always ground; the checker receives
-- @theta@ explicitly (no unification in the trusted core). Placeholder as an
-- association list.
type Subst = [(Param, Term)]

-- | A support term (spec §6), the single syntactic category for arguments:
--
-- > w ::= leaf l
-- >     | r⟨theta ; w1, …, wn ; {q ↦ w_q} ; {o*} ; assurance⟩
--
-- Mode comes from the rule's declaration in the policy, not from the term. A
-- defeasible instance carries @assurance = AssuranceNone@ and may have a
-- discharge map and open holes; a strict instance has an empty discharge map and
-- hole set and assurance exactly 'AssuranceTrusted' or 'AssuranceCert'.
data SupportTerm
  = SLeaf LeafId
  | SRule
      { srRule :: RuleId
      , srSubst :: Subst
      , srPremises :: [SupportTerm]
      , srDischarge :: [(QuestionId, SupportTerm)] -- ^ @{q ↦ w_q}@
      , srHoles :: [ObligationId] -- ^ explicitly open obligations
      , srAssurance :: Assurance
      }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Positional attacks (spec §7)
-- ---------------------------------------------------------------------------

-- | A single step in a position path (spec §7): a premise index or a
-- critical-question name. @π ::= ε | π.i | π.q@.
data Step = StepPremise Int | StepQuestion QuestionId
  deriving (Eq, Show)

-- | A position @π@ in a support term: the empty path is the root (its
-- conclusion). @w\@π@ is the subterm occurrence at @π@.
type Position = [Step]

-- | A typed positional attack (spec §7). The three kinds are exactly the three
-- kinds of positions in a term: the root conclusion, an internal rule
-- occurrence, and a frontier leaf.
--
-- > k ::= rebut w u          -- targets the root conclusion of u (defeasible only)
-- >     | undercut w u@π      -- targets the rule occurrence at π in u
-- >     | undermine w u@π     -- targets the leaf occurrence at π in u
data Attack
  = Rebut ArgId ArgId
  | Undercut ArgId ArgId Position
  | Undermine ArgId ArgId Position
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Programs (spec §2, §4.4)
-- ---------------------------------------------------------------------------

-- | A content digest (artifact snapshot, policy version, theory) — part of
-- replay identity (spec §2).
newtype Digest = Digest String deriving (Eq, Ord, Show)

-- | The presentation-syntax target of a @challenges(…)@ argument conclusion
-- (spec §7 defeat layer; presentation-only, __not__ a checker input).
--
-- An argument authored purely to attack another names, in surface form, /what/
-- it challenges. This is human-facing intent recorded verbatim by the parser;
-- the argument's real conclusion (what the checker sees, spec §6.1) is still its
-- support term's conclusion, and the actual defeat edge is the separate typed
-- 'Attack' line ('Rebut'\/'Undercut'\/'Undermine'). The elaborator (M4a A1) uses
-- the target only for diagnostics, never to build the AF.
--
-- The two surface forms mirror the two attackable non-root positions (spec §7):
--
-- > challenges(external_validity(a1))   -- ChallengesQuestion external_validity a1
-- > challenges(e6)                      -- ChallengesLeaf e6
data ChallengeTarget
  = -- | @challenges(q(u))@: the critical question @q@ of argument @u@ (the CQ
    -- discharge position @u\@π.q@, spec §4.2). Pairs with an 'Undercut'\/'Undermine'.
    ChallengesQuestion QuestionId ArgId
  | -- | @challenges(l)@: a frontier evidence leaf @l@. Pairs with an 'Undermine'.
    ChallengesLeaf LeafId
  deriving (Eq, Show)

-- | The conclusion an @arg@ declaration announces (spec §4.4, §7). A
-- presentation-only sum: the checker consumes only the support term's own
-- 'concl' (spec §6.1), so which arm is used never changes the compiled AF — it
-- records the /author's stated role/ for the argument, which the elaborator
-- resolves and validates.
--
-- > arg a  : supports(c1)                        -- SupportsClaim  (c1 declared)
-- > arg d3 : supports(c1_neg)                     -- SupportsDerived (c1_neg NOT declared)
-- > arg d1 : challenges(external_validity(a1))    -- Challenges …
data ArgConcl
  = -- | @supports(c)@ where @c@ is a declared 'Claim'; the elaborator checks
    -- @concl(w) ≡ c.claimFormal@ (spec §3.1).
    SupportsClaim PropId
  | -- | @supports(c)@ where the named id is __not__ a declared claim: its formal
    -- proposition is /derived by the elaborator/ (A1) from the support term's
    -- conclusion. A0.5 records only the surface label; no claim status is
    -- requested for it unless a separate @status@ declaration names it.
    SupportsDerived PropId
  | -- | @challenges(…)@: an argument whose reason for existing is to attack. Its
    -- conclusion for the Unit is still its support term's conclusion; the target
    -- is presentation intent (see 'ChallengeTarget').
    Challenges ChallengeTarget
  deriving (Eq, Show)

-- | An @arg@ declaration naming a support term and the conclusion it announces
-- (spec §4.4).
--
-- > arg a : <arg-conclusion> by <support term>
--
-- Multiple independent supports for the same claim are separate 'Arg's — never
-- merged into one term — so defeat can eliminate one while another survives.
data Arg = Arg
  { argId :: ArgId
  , argConcl :: ArgConcl
  , argTerm :: SupportTerm
  }
  deriving (Eq, Show)

-- | A top-level program declaration (spec §2). Leaves, claims, arguments, and
-- attacks; @status c@ requests a claim's status.
data Decl
  = DeclLeaf Leaf
  | DeclClaim Claim
  | DeclArg Arg
  | DeclAttack Attack
  | DeclStatus PropId
  | DeclGroup DupGroup -- ^ a duplicate-report group (spec §4.3)
  deriving (Eq, Show)

-- | A LARA program (spec §2):
--
-- > P ::= artifact A at digest
-- >       policy Pi
-- >       use backends [beta@version*]
-- >       declaration*
--
-- Checked against a fixed proposition signature @Sigma@, the versioned policy
-- 'programPolicy', the backend registry @R@, and the artifact snapshot named by
-- 'programArtifact' / 'programDigest'.
data Program = Program
  { programArtifact :: String
  , programDigest :: Digest
  , programPolicy :: PolicyId
  , programBackends :: [(BackendId, String)] -- ^ @[beta@version]@
  , programDecls :: [Decl]
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Checker-boundary units (the M3 wire anchor)
-- ---------------------------------------------------------------------------

-- | A checker-boundary unit: exactly the data the executable checker consumes,
-- mirroring @lean/Lara/Unit.lean@ ('Lara.Unit') plus its environment inputs
-- (the leaf context @Gamma@ and the closed backend-registry theory table).
-- This is the shape the S-expression wire codec ("Lara.Wire", the N11
-- differential anchor) decodes to; the richer presentation-layer 'Program'
-- (artifact digests, claim NL text and bindings, leaf kinds) elaborates to it.
--
-- Attacks reference arguments by 'ArgId' (spec §2: @a@, @w@, @u@ are argument
-- identifiers); resolution to terms is a decode-boundary step both drivers
-- perform identically: argument identifiers must be unique and every attack
-- endpoint must be declared. Those two invariants are wire well-formedness
-- (R14), not checker rejection classes.
data Unit = Unit
  { unitRules :: [Rule] -- ^ policy rules, declaration order (ids inline)
  , unitContraries :: [Contrary] -- ^ the policy's @contrary@ pairs
  , unitExceptions :: [Exception] -- ^ the policy's @exception@ declarations
  , unitTheories :: [(TheoryDigest, [Prop])] -- ^ theory table for @nd\@1@ (closed registry)
  , unitLeaves :: [(LeafId, Prop)] -- ^ the leaf context @Gamma@ (pre-group filter)
  , unitArgs :: [(ArgId, SupportTerm)] -- ^ named arguments, declaration order
  , unitAttacks :: [Attack] -- ^ declared typed attacks (id-based)
  , unitQueries :: [Prop] -- ^ claim atoms whose status is requested
  , unitGroups :: [DupGroup] -- ^ duplicate-report groups (spec §4.3)
  , unitGroupMode :: GroupConflictMode -- ^ conflict outcome; default 'QuarantineOnConflict'
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Claim status (spec §8)
-- ---------------------------------------------------------------------------

-- | The four-state grounded claim label computed on one checked framework
-- (spec §8). The public driver may demote this to the conditional payload of
-- @evidence-blocked@ when quarantine edited the framework under the query; see
-- "Lara.Wire".'Lara.Wire.PublicStatus'.
--
-- * 'Gap' — no support, or an unresolved hole no complete alternative closes.
-- * 'Justified' — some complete support argument is labelled @in@.
-- * 'Contested' — none @in@, some @undec@.
-- * 'Defeated' — support is nonempty and every argument is @out@.
data Status = Gap | Justified | Contested | Defeated
  deriving (Eq, Ord, Show)

-- | A grounded argument label (spec §8): the grounded labelling maps each
-- compiled argument to @in@, @out@, or @undec@.
data Label = LIn | LOut | LUndec
  deriving (Eq, Ord, Show)

-- ---------------------------------------------------------------------------
-- Rejection outcomes (spec §10.1)
-- ---------------------------------------------------------------------------

-- | The frozen rejection classes decidable by the executable checker (spec
-- §10.1; mirrors @lean/Lara/Check/Error.lean@ 'RejectClass'). R9
-- (data-integrity) is decided at the driver boundary before @checkUnit@ — an
-- escalated duplicate-report-group conflict (spec §4.3), like R13's replay
-- preflight. R2 (signature) and R8 (admission) remain outside the executable
-- core; R14 (codec) is reported at the decode boundary, never as a verdict.
data RejectClass = R1 | R3 | R4 | R5 | R6 | R7 | R9 | R10 | R11 | R12 | R13
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | A unit-level rejection outcome (mirrors @lean/Lara/Check/Unit.lean@
-- 'UnitError' and @lean/Lara/Check/Program.lean@ 'ProgramError'): either a
-- frozen rejection class or a structural program-boundary outcome that has no
-- R-class by design.
data Rejection
  = RejectClass RejectClass
  | DuplicateRule -- ^ duplicate policy rule identifier
  | DuplicateArgument -- ^ two structurally identical argument terms
  | IncompleteArgument -- ^ an argument with open root obligations
  | MissingConflict -- ^ an undeclared contrary pair between complete arguments
  deriving (Eq, Ord, Show)
