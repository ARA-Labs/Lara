-- | The static code-inspection domain-checker backend: @insp\@1@
-- (@docs\/insp1-code-inspection-decision.md@; @docs\/strict-backend-decision.md@
-- §2 obligations; spec §5.2 portfolio item 3).
--
-- This adapter certifies the corpus's third measured strict shape — structural
-- facts about referenced source — as a closed four-predicate family over
-- __declared exhaustive inventories__:
--
-- > code_absent(Src, Feat)                     -- Feat occurs nowhere in Src
-- > code_present(Src, Feat)                    -- Feat occurs in Src
-- > code_unique(Src, Feat)                     -- Feat is the only thing found in Src
-- > code_planned_not_shipped(Plan, Src, Feat)  -- in the plan, absent from the source
--
-- The last member is the corpus's own scheme name (@plan_vs_shipped_diff@,
-- M0 C13\/C14: 3 of 60 sampled claims), and the family it heads is the
-- @code_inspection@ family of the spec §4.5 reference vocabulary.
--
-- == What makes this a /strict/ step: the closed-world move
--
-- A negative existential over code — \"the shipped module has no repair call
-- site anywhere\" — is not an observation. It is an __inference from an
-- exhaustive enumeration__: /given/ that the inspection covered the whole
-- module and enumerated everything it found, the conclusion that a feature is
-- absent follows deductively. That step is what this backend replays, and it
-- is the only thing it replays.
--
-- The enumeration itself arrives as an ordinary premise:
--
-- > inv(Src, finding(f1, finding(f2, no_findings)))
--
-- read as \"an exhaustive inspection of @Src@ found exactly @f1@ and @f2@\".
-- The empty inventory @inv(Src, no_findings)@ — inspected, found nothing — is
-- the pure negative-existential case, and 'holdsRel' accepts every absence
-- against it.
--
-- The list is a source-level cons spine rather than a variadic constructor
-- because @Σ@ fixes each constructor's arity (spec §2): @inv@\/2,
-- @finding@\/2, @no_findings@\/0 are three fixed-arity symbols, so a unit's
-- signature can declare them and the sort checker (R2) can check them.
--
-- == Certificates
--
-- > cert ::= (inspect (prem N))                 -- the one-inventory members
-- >        | (inspectdiff (prem N) (prem M))    -- the plan-vs-shipped diff
--
-- @N@ and @M@ name the premise slots supplying the inventories (dependency
-- accountability, obligation 4: @uses@ is a function of the certificate
-- alone). As in @ord\@1@ the relation is read off the goal predicate, not the
-- certificate, and there is __no witness value__: the certificate names slots
-- and nothing else. What the certificate /does/ fix is the arity of the step,
-- which is why the family's two shapes get two wire keywords: an
-- @(inspect …)@ payload under a @code_planned_not_shipped@ goal is a
-- rejection, not a re-interpretation.
--
-- == What this discharges — and what it does not
--
-- An accepted certificate certifies that each cited premise carries an
-- inventory of the source unit the goal names, and that the goal's structural
-- statement holds of the enumerated findings. It does __not__ assert that any
-- inventory is /faithful to the bytes/ — that the inspection really was
-- exhaustive, or that it read the version of the source the claim is about.
-- This is the factivity firewall in its sharpest form for this backend:
-- byte-level evidence admission is not part of v0.1 (spec §4.3), so an
-- inventory is an @evidence declared@ leaf like any measurement, and it stays
-- defeasible — attackable, quarantinable, admission-governed. The corpus's own
-- @plan_vs_shipped_diff@ unit
-- (@corpus-units\/rebench-rust_codecontests\/C09@) is exactly a case where the
-- coverage half is met and the version half is not; the honest verdict there
-- is a @gap@, and no certificate changes that.
--
-- What the adapter removes from the trusted base is narrower and real: the
-- step from an enumeration to a structural conclusion no longer rests on a
-- trusted policy rule.
--
-- == Premise-only slots
--
-- This backend rejects any slot @>= nPrem@, the seam-wide rule @ra\@1@ and
-- @ord\@1@ already follow (\"Lara.Strict.Ord\" §\"Premise-only slots\"). On the
-- raw @.sexp@ door the backend theory table is built from the unit's own wire
-- @theories@ section and replay preflight never validates its content, so a
-- theory-entry slot would let an artifact supply the very inventory it then
-- certifies against — the closed-world premise self-supplied, which is the one
-- thing this backend must never allow. The Lean counterpart reaches the same
-- acceptance set from the other side: @Lara.Driver.buildRegistry@ resolves any
-- /known/ @insp\@1@ digest to @[]@, so there the consulted context genuinely
-- is the premises alone.
--
-- == Contraries, unlike @ord\@1@
--
-- @num_lt@\/@num_le@ head no declared contrary pair because comparison goals
-- are decided against a /shared/ ground truth (the numerals in the goal), so a
-- sound backend can never accept two conflicting members. Inspection goals are
-- not: they are decided against a __declared__ inventory, and two units may
-- declare different inventories for the same source. @code_absent@ and
-- @code_present@ over the same @(Src, Feat)@ are therefore genuinely
-- co-acceptable, and the policy must declare them a contrary pair so the
-- conflict surfaces as an attack. The Lean development states both halves:
-- @inspModels_excl_of_same_entry@ (exclusive when the two arguments read the
-- same inspection leaf) and @inspModels_absent_present_sat@ (jointly
-- satisfiable when they do not).
module Lara.Strict.Insp
  ( -- * Backend formulas and certificates
    InspRel (..)
  , InspGoal (..)
  , InspCert (..)
  , Inventory (..)
    -- * Wire grammar
  , Tag (..)
  , tagToString
  , parseTag
  , decodeCert
    -- * Source-level inventory vocabulary
  , Con (..)
  , conToString
  , parseCon
    -- * Parsing and evaluation (the replay)
  , inspPred
  , parseInspPred
  , diffPred
  , parseGoal
  , premiseInventory
  , holdsRel
    -- * The registered adapter
  , inspBackendId
  , slotSchemaOne
  , slotSchemaDiff
  , mkInspBackend
  ) where

import qualified Data.Set as Set

import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..), nf, prettyTerm)
import Lara.Strict
  ( Backend (..)
  , BackendId (..)
  , Dependency (..)
  , SExpr (..)
  , TheoryDigest
  )
import Lara.Strict.Cell (SlotSchema (..), decodeSlot)

-- ---------------------------------------------------------------------------
-- Backend formulas and certificates
-- ---------------------------------------------------------------------------

-- | The closed one-inventory goal family: the three statements a single
-- exhaustive enumeration settles. The concrete spellings live in exactly one
-- table ('inspPred'); the two-inventory diff has its own ('diffPred').
data InspRel
  = -- | @code_absent(Src, Feat)@: @Feat@ is in no finding of @Src@
    IAbsent
  | -- | @code_present(Src, Feat)@: @Feat@ is among the findings of @Src@
    IPresent
  | -- | @code_unique(Src, Feat)@: the findings of @Src@ are nonempty and all
    -- of them are @Feat@ — the \"single active config\" shape
    IUnique
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The goal shape this backend certifies, parsed from the normalized goal
-- proposition.
data InspGoal
  = -- | a one-inventory member over @(Src, Feat)@
    GoalOne InspRel Term Term
  | -- | @code_planned_not_shipped(Plan, Src, Feat)@: the two-inventory diff
    GoalDiff Term Term Term
  deriving (Eq, Show)

-- | A code-inspection certificate: which __premise__ slots carry the cited
-- inventories. No witness value — the structural statement is decided by
-- replay against the enumerations.
data InspCert
  = -- | @(inspect (prem N))@
    CertOne Int
  | -- | @(inspectdiff (prem N) (prem M))@: the plan slot, then the source slot
    CertDiff Int Int
  deriving (Eq, Show)

-- | A decoded inventory: the inspected source unit and the exhaustive list of
-- findings. The list order is the author's; nothing in the family depends on
-- it, and repeated findings are harmless.
data Inventory = Inventory
  { invSource :: Term -- ^ the inspected source unit
  , invFindings :: [Term] -- ^ everything the inspection found, exhaustively
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- Wire grammar (the closed decoder)
-- ---------------------------------------------------------------------------

-- The certificate reaches the adapter as an opaque 'SExpr'; only this module
-- decodes it (closed registration). The @(prem N)@ slot-reference sub-grammar
-- is seam-shared and lives in "Lara.Strict.Cell" ('decodeSlot'); this table
-- keeps only the @insp\@1@-specific keywords.

-- | The closed set of @insp\@1@-specific wire keywords
-- ('Lara.Strict.ND.Tag' discipline).
data Tag = TInspect | TInspectDiff
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The on-the-wire spelling of a keyword.
tagToString :: Tag -> String
tagToString TInspect = "inspect"
tagToString TInspectDiff = "inspectdiff"

-- | Parse a wire keyword, inverse to 'tagToString'.
parseTag :: String -> Maybe Tag
parseTag s = lookup s [(tagToString t, t) | t <- [minBound .. maxBound]]

-- | Decode the opaque wire certificate; rejects unknown tags, wrong arity, and
-- non-canonical slot naturals.
decodeCert :: SExpr -> Either String InspCert
decodeCert (SList [SAtom k, slot])
  | parseTag k == Just TInspect = CertOne <$> decodeSlot "insp" slot
decodeCert (SList [SAtom k, slotP, slotS])
  | parseTag k == Just TInspectDiff =
      CertDiff <$> decodeSlot "insp" slotP <*> decodeSlot "insp" slotS
decodeCert e = Left ("malformed insp certificate: " ++ show e)

-- ---------------------------------------------------------------------------
-- Source-level inventory vocabulary
-- ---------------------------------------------------------------------------

-- | The closed set of source constructor spellings the inventory convention
-- reserves. These are /source/ symbols, not wire keywords — a unit declares
-- them in its @Σ@ and the sort checker checks them — but they obey the same
-- one-table discipline: the concrete spelling of each lives here and nowhere
-- else.
data Con
  = -- | @inv(Src, Findings)@: an exhaustive inspection of @Src@
    CInv
  | -- | @finding(F, Rest)@: one enumerated finding, then the rest
    CFinding
  | -- | @no_findings@: the end of the enumeration (alone: found nothing)
    CNoFindings
  deriving (Eq, Ord, Show, Enum, Bounded)

-- | The source spelling of an inventory constructor.
conToString :: Con -> String
conToString CInv = "inv"
conToString CFinding = "finding"
conToString CNoFindings = "no_findings"

-- | Recognize an inventory constructor, inverse to 'conToString'.
parseCon :: FunSym -> Maybe Con
parseCon (FunSym s) = lookup s [(conToString c, c) | c <- [minBound .. maxBound]]

-- ---------------------------------------------------------------------------
-- Parsing and evaluation (the replay)
-- ---------------------------------------------------------------------------

-- | The goal predicate spelling each one-inventory family member is authored
-- with. This is the one table where those spellings live.
inspPred :: InspRel -> Pred
inspPred IAbsent = Pred "code_absent"
inspPred IPresent = Pred "code_present"
inspPred IUnique = Pred "code_unique"

-- | Recognize a one-inventory family predicate, inverse to 'inspPred'.
parseInspPred :: Pred -> Maybe InspRel
parseInspPred p = lookup p [(inspPred r, r) | r <- [minBound .. maxBound]]

-- | The two-inventory diff predicate — the corpus's @plan_vs_shipped_diff@
-- shape, spelled for the domain reader (spec §4.5 naming taste).
diffPred :: Pred
diffPred = Pred "code_planned_not_shipped"

-- | Parse the normalized goal into an 'InspGoal'. Arity is part of the
-- family: a one-inventory predicate at arity 3, or the diff predicate at
-- arity 2, is not this backend's goal shape.
parseGoal :: Prop -> Either String InspGoal
parseGoal g =
  case nf g of
    Prop p [src, feat]
      | Just rel <- parseInspPred p -> Right (GoalOne rel src feat)
    Prop p [plan, src, feat]
      | p == diffPred -> Right (GoalDiff plan src feat)
    other -> Left ("goal is not a code-inspection atom: " ++ show other)

-- | Every @inv(…)@ node anywhere in a term, outermost first. The scan does
-- __not__ stop at a match: a nested @inv@ inside a finding is a second node
-- and 'premiseInventory' rejects the premise for it, which is what keeps
-- \"the premise carries one inventory\" unambiguous.
invNodes :: Term -> [Term]
invNodes t = case t of
  TNum _ -> []
  TStr _ -> []
  TCon k ts -> here ++ concatMap invNodes ts
    where
      here = [t | parseCon k == Just CInv]

-- | Parse the finding spine @finding(F1, finding(…, no_findings))@ into the
-- enumerated findings. Anything else — a wrong arity, a foreign constructor,
-- a literal in tail position — is a rejection: the adapter refuses to guess
-- how far the enumeration reached.
parseFindings :: Term -> Either String [Term]
parseFindings t = case t of
  TCon k [] | parseCon k == Just CNoFindings -> Right []
  TCon k [f, rest] | parseCon k == Just CFinding -> (f :) <$> parseFindings rest
  _ -> Left ("malformed inventory finding list at: " ++ prettyTerm t)

-- | The inventory convention: the normalized premise proposition must contain
-- exactly one @inv(Src, Findings)@ node anywhere in its argument terms, and
-- that node's second argument must be a well-formed finding spine.
--
-- The \"exactly one\" discipline is 'Lara.Strict.Cell.premiseCell'\'s, for the
-- same reason: a premise carrying two inventories does not say which one the
-- certificate meant, and guessing is how a checker becomes unsound quietly.
premiseInventory :: Prop -> Either String Inventory
premiseInventory p =
  case nf p of
    normalized@(Prop _ ts) ->
      case concatMap invNodes ts of
        [TCon _ [src, findings]] -> Inventory src <$> parseFindings findings
        [node] ->
          Left ("inventory node is not inv(Src, Findings): " ++ prettyTerm node)
        nodes ->
          Left
            ( "premise must carry exactly one inventory, found "
                ++ show (length nodes)
                ++ " in "
                ++ show normalized
            )

-- | The one-inventory replay: a decidable statement about the enumerated
-- findings.
--
-- 'IAbsent' over an empty inventory is the pure negative existential — an
-- exhaustive inspection that found nothing certifies every absence — and is
-- exactly the closed-world step this backend exists to replay.
holdsRel :: InspRel -> [Term] -> Term -> Bool
holdsRel IAbsent fs f = f `notElem` fs
holdsRel IPresent fs f = f `elem` fs
holdsRel IUnique fs f = not (null fs) && all (== f) fs

-- | The prose name of a family member, for rejection messages only. The
-- authored spelling stays 'inspPred'; this is prose, not wire syntax.
relPhrase :: InspRel -> String
relPhrase IAbsent = "absent from"
relPhrase IPresent = "present in"
relPhrase IUnique = "the sole finding of"

-- ---------------------------------------------------------------------------
-- The registered adapter
-- ---------------------------------------------------------------------------

-- | The static code-inspection backend identifier: @insp\@1@.
inspBackendId :: BackendId
inspBackendId = BackendId {backendName = "insp", backendVersion = 1}

-- | The one-inventory premise-reference schema: @(inspect (prem N))@.
-- Spellings come from this module's own tag table and identity — the schema
-- introduces no new strings.
slotSchemaOne :: SlotSchema
slotSchemaOne =
  SlotSchema
    { ssBackend = inspBackendId
    , ssHead = tagToString TInspect
    , ssArity = 1
    , ssRefSlots = [0]
    }

-- | The plan-vs-shipped diff schema: @(inspectdiff (prem N) (prem M))@, both
-- positions premise references. Two schemas, one per wire keyword: they share
-- a backend but differ in head and arity, which is what
-- "Lara.Elaborate.CertSlots" matches on.
slotSchemaDiff :: SlotSchema
slotSchemaDiff =
  SlotSchema
    { ssBackend = inspBackendId
    , ssHead = tagToString TInspectDiff
    , ssArity = 2
    , ssRefSlots = [0, 1]
    }

-- | Build the adapter with a __fixed__ theory table ('Lara.Strict.RA.mkRABackend'
-- discipline: closed registration, digest selection only). The theory is empty
-- by design and its entries are never consulted — every inventory must trace
-- to a premise — so an accepted certificate reports only 'PremiseSlot'
-- dependencies; an unknown digest is still a rejection.
mkInspBackend :: [(TheoryDigest, [Prop])] -> Backend
mkInspBackend theories =
  Backend
    { backendId = inspBackendId
    , runBackend = run
    }
  where
    run :: TheoryDigest -> [Prop] -> Prop -> SExpr -> Either String (Set.Set Dependency)
    run digest premises goal certSExpr =
      case lookup digest theories of
        Nothing -> Left ("unknown theory digest: " ++ show digest)
        Just theoryProps -> do
          cert <- decodeCert certSExpr
          goalI <- parseGoal goal
          case (cert, goalI) of
            (CertOne n, GoalOne rel src feat) -> do
              inv <- inventoryAt theoryProps n
              assert
                (invSource inv == src)
                ( "inventory premise inspects a different source unit: premise "
                    ++ prettyTerm (invSource inv)
                    ++ " vs goal "
                    ++ prettyTerm src
                )
              assert
                (holdsRel rel (invFindings inv) feat)
                ( "the claimed structural fact does not hold: "
                    ++ prettyTerm feat
                    ++ " is not "
                    ++ relPhrase rel
                    ++ " the inspected findings of "
                    ++ prettyTerm src
                )
              Right (Set.fromList [PremiseSlot n])
            (CertDiff n m, GoalDiff plan src feat) -> do
              planInv <- inventoryAt theoryProps n
              srcInv <- inventoryAt theoryProps m
              assert
                (invSource planInv == plan)
                ( "plan-side inventory premise inspects a different unit: premise "
                    ++ prettyTerm (invSource planInv)
                    ++ " vs goal "
                    ++ prettyTerm plan
                )
              assert
                (invSource srcInv == src)
                ( "source-side inventory premise inspects a different unit: premise "
                    ++ prettyTerm (invSource srcInv)
                    ++ " vs goal "
                    ++ prettyTerm src
                )
              assert
                (holdsRel IPresent (invFindings planInv) feat)
                ( "the planned half fails: "
                    ++ prettyTerm feat
                    ++ " is not among the findings of "
                    ++ prettyTerm plan
                )
              assert
                (holdsRel IAbsent (invFindings srcInv) feat)
                ( "the not-shipped half fails: "
                    ++ prettyTerm feat
                    ++ " is among the findings of "
                    ++ prettyTerm src
                )
              -- A same-slot certificate dedups to a single dependency (and
              -- cannot be accepted: one inventory cannot both hold and miss
              -- the feature).
              Right (Set.fromList [PremiseSlot n, PremiseSlot m])
            (CertOne _, GoalDiff{}) ->
              Left
                ( "certificate cites one inventory but the goal is a "
                    ++ show diffPred'
                    ++ " diff over two"
                )
            (CertDiff _ _, GoalOne{}) ->
              Left
                ( "certificate cites two inventories but the goal is a"
                    ++ " one-inventory code-inspection atom"
                )
      where
        nPrem = length premises

        diffPred' = case diffPred of Pred s -> s

        -- Premise-only slot resolution, identical in shape and message to
        -- @ord\@1@'s and @ra\@1@'s: a slot naming a theory entry is rejected
        -- outright. Here the guard carries more weight than in either sibling,
        -- because the value it protects is the closed-world premise itself: a
        -- self-supplied theory entry could assert "I inspected everything and
        -- found nothing" and no leaf or admission check would ever see it.
        --
        -- The @i >= 0@ conjunct keeps this total for the same reason it does
        -- in "Lara.Strict.Ord": 'decodeSlot' parses a canonical natural, so a
        -- negative index never arrives, but dropping the conjunct would turn a
        -- rejection into a @premises !! (-1)@ exception.
        resolve theoryProps i
          | i >= 0 && i < nPrem = Right (premises !! i)
          | i >= nPrem && i < nPrem + length theoryProps =
              Left
                ( "insp cites premise slots only; slot names theory entry "
                    ++ show (i - nPrem)
                )
          | otherwise = Left ("premise slot out of range: " ++ show i)

        inventoryAt theoryProps i = resolve theoryProps i >>= premiseInventory

        assert cond msg = if cond then Right () else Left msg
