-- | The seven-stage whole-unit checker (spec §10) — the Haskell mirror of
-- @lean/Lara/Check/Unit.lean@ (@checkUnit@) and
-- @lean/Lara/Check/Program.lean@ (@checkProgramDetailed@).
--
-- 'checkUnit' is the canonical executable acceptance boundary. Its public
-- seven-stage order is exactly the Lean one:
--
--   1. duplicate rule identifiers ('Lara.Policy.firstDuplicateRuleId')
--   2. R2 signature well-formedness and well-sortedness
--      ('Lara.Sigma.WellSorted.unitSortError')
--   3. R12 policy well-formedness ('Lara.Policy.firstViolation')
--   4. duplicate arguments ('firstDuplicate')
--   5. support ('Lara.SupportTerm.inferSupport')
--   6. typed attacks ('Lara.Attack.checkAttack')
--   7. missing conflict ('firstMissingConflictInfo')
--
-- The first three stages run before program checking; the remaining four are
-- the detailed program checker's fixed order.
--
-- __Why the sort stage is at position 2__ (@lara-core\@0.2@). Σ conformance
-- is a precondition for reading the policy as patterns at all: both the R12
-- Path-B validator and support inference instantiate patterns, and both should
-- be entitled to assume well-sortedness rather than re-derive it. Running it
-- after duplicate-rule detection means the stage never has to reason about
-- which of two same-named rules it is checking.
--
-- A successful check retains the
-- checked-node cache ('cuNodes') and the compiled program ('cuProgram'), so
-- "Lara.Compile" and "Lara.Grounded" consume them without re-inferring support
-- (the Lean @CheckedUnit@ / @ProgramAcceptance@ carry @nodes@ and
-- @attack_complete@; the missing-conflict scan is the executable witness of
-- attack completeness).
module Lara.Check
  ( -- * Located program-level diagnostics (Lean @Program.lean@)
    DeclLoc (..)
  , MissingConflictInfo (..)
  , ProgramError (..)
  , programErrorClass
    -- * Whole-unit diagnostics (Lean @Check.Unit.UnitError@)
  , UnitError (..)
  , unitErrorClass
    -- * Accepted unit (Lean @Unit.CheckedUnit@)
    -- | Opaque: the constructor is hidden so an accepted unit cannot be forged;
    -- 'checkUnit' is its sole producer (see "Lara.Check.Internal"). Read via
    -- 'cuProgram' \/ 'cuNodes'.
  , CheckedUnit
  , cuProgram
  , cuNodes
    -- * Structural duplicate detection
  , firstDuplicate
    -- * Checker configuration (ablation switches)
  , CheckConfig (..)
  , fullConfig
  , noCQConfig
  , noTypedConfig
  , noConflictScanConfig
    -- * The detailed program checker and its conflict scan
  , ProgramAcceptance (..)
  , ConflictNode (..)
  , conflictCache
  , firstMissingConflictInfo
  , checkProgramDetailed
    -- * Attack resolution and the public boundary
  , resolveAttacks
  , checkUnit
  , checkUnitWith
  ) where

import Data.Maybe (mapMaybe)

import Lara.AST
import Lara.Attack
  ( DefeatPolicy (..)
  , RAttack (..)
  , checkAttack
  , contraryMatchB
  , rSource
  , rTarget
  )
import Lara.Check.Internal (CheckedUnit (..))
import Lara.Compile
  ( conflictAttackableB
  , coveredB
  )
import Lara.Compile.Internal (CheckedProgram (..))
import Lara.Policy
  ( DuplicateRuleId
  , Violation
  , firstDuplicateRuleId
  , firstViolation
  , lookupRule
  )
import Lara.Prop (Prop)
import Lara.Sigma.WellSorted (SortError, unitSortError)
import Lara.SupportTerm
import Lara.SupportTerm.Internal (CheckedNode (..))

-- ---------------------------------------------------------------------------
-- Located program-level diagnostics (Lean @lean/Lara/Check/Program.lean@)
-- ---------------------------------------------------------------------------

-- | Where a program-level rejection is located (Lean @DeclLoc@).
data DeclLoc = DLArgument Int | DLAttack Int
  deriving (Eq, Show)

-- | An undeclared attackable contrary pair between complete arguments (Lean
-- @Program.MissingConflictInfo@).
data MissingConflictInfo = MissingConflictInfo
  { mcSourceIndex :: Int
  , mcTargetIndex :: Int
  , mcSourceConclusion :: Prop
  , mcTargetConclusion :: Prop
  }
  deriving (Eq, Show)

-- | A program-boundary rejection (Lean @ProgramError@). Only wrapped frozen
-- checker failures ('PERejection') carry an R-class; the structural outcomes do
-- not (they are program-boundary outcomes with no frozen class by design).
data ProgramError
  = PERejection DeclLoc CheckError
  | PEDuplicateArgument Int Int
  | PEIncompleteArgument Int [QuestionId]
  | PEMissingConflict MissingConflictInfo
  deriving (Eq, Show)

-- | The frozen rejection class of a program error, if any (Lean
-- @ProgramError.rejectClass@).
programErrorClass :: ProgramError -> Maybe RejectClass
programErrorClass e = case e of
  PERejection _ ce -> Just (checkErrorClass ce)
  PEDuplicateArgument _ _ -> Nothing
  PEIncompleteArgument _ _ -> Nothing
  PEMissingConflict _ -> Nothing

-- ---------------------------------------------------------------------------
-- Whole-unit diagnostics (Lean @Check.Unit.UnitError@)
-- ---------------------------------------------------------------------------

-- | Closed diagnostics for whole-unit acceptance (Lean @UnitError@).
data UnitError
  = UEDuplicateRule DuplicateRuleId
  | UESignature SortError
  | UEPolicyViolation Violation
  | UEProgram ProgramError
  deriving (Eq, Show)

-- | The frozen rejection class of a unit error, if any (Lean
-- @UnitError.rejectClass@): only R12 and wrapped frozen checker failures have a
-- class; duplicate-rule preserves its typed payload without a frozen class.
unitErrorClass :: UnitError -> Maybe RejectClass
unitErrorClass e = case e of
  UEDuplicateRule _ -> Nothing
  UESignature _ -> Just R2
  UEPolicyViolation _ -> Just R12
  UEProgram pe -> programErrorClass pe

-- Accepted unit (Lean @Unit.CheckedUnit@): the type is defined in
-- "Lara.Check.Internal" and re-exported abstractly above; 'checkUnit' below is
-- its sole construction site.

-- ---------------------------------------------------------------------------
-- Structural duplicate detection (Lean @firstDuplicate@)
-- ---------------------------------------------------------------------------

-- | The first structurally-identical pair of argument terms, as
-- @(earlier, later)@ indices (Lean @firstDuplicate@). @Nothing@ iff the list is
-- duplicate-free.
firstDuplicate :: [SupportTerm] -> Maybe (Int, Int)
firstDuplicate = go 0
  where
    go _ [] = Nothing
    go i (w : ws) = case firstEqualIndex w (i + 1) ws of
      Just j -> Just (i, j)
      Nothing -> go (i + 1) ws
    firstEqualIndex _ _ [] = Nothing
    firstEqualIndex w j (x : xs)
      | w == x = Just j
      | otherwise = firstEqualIndex w (j + 1) xs

-- ---------------------------------------------------------------------------
-- Checker configuration (ablation switches)
-- ---------------------------------------------------------------------------

-- | Ablation switches over the detailed program checker. Each flag only ever
-- /removes/ a rejection arm, so @accept(fullConfig) ⊆ accept(cfg)@ for every
-- @cfg@. The config never reaches the support kernel ('inferSupport' and the
-- R3–R7 rules run unconditionally) and is never carried on the wire: it exists
-- only at the checker boundary, for the M5 ablation baselines.
--
-- __Where that inclusion is enforced.__ In Haskell, by
-- @test\/AblationSpec.hs@'s @prop_monotonicity@, over every manifest input and
-- over all 8 inhabitants of this record (its @allConfigs@ — not merely the
-- three named baselines of 'Lara.Measure.ablationConfigs', which are the
-- reporting vocabulary). It is deliberately NOT a Lean obligation: the Lean
-- development mechanizes the frozen semantics, which is 'fullConfig' alone, and
-- a checker-boundary flag owes an @AxCheck.lean@ entry only if it changes what
-- 'fullConfig' accepts — which by construction it must not.
--
-- That scope rule, the six @AxCheck.lean@ entries that pin the conflict scan
-- independently of this switch, and the rejected alternative are recorded in
-- @docs\/mechanization-scope-decision.md@.
data CheckConfig = CheckConfig
  { ccObligationGate :: Bool
    -- ^ Enforce the open-obligation gate ('PEIncompleteArgument' in
    -- 'checkArguments'). Off, an argument with open critical-question
    -- obligations is retained instead of rejected.
  , ccTypedAttacks :: Bool
    -- ^ Enforce the per-attack 'checkAttack' typing in 'checkAttacks'. Off,
    -- attacks still must reference declared arguments (R1), but are not typed.
  , ccConflictScan :: Bool
    -- ^ Enforce the 'firstMissingConflictInfo' completeness scan. Off, an
    -- attackable contrary pair between complete arguments may go undeclared.
    --
    -- Separate from 'ccTypedAttacks' because the two answer different
    -- questions: typing asks whether a /declared/ edge is licensed, the scan
    -- asks whether every /required/ edge is declared. Folded together, no
    -- ablation cell isolated the scan, which is the executable witness of the
    -- attack-completeness theorem.
  }
  deriving (Eq, Show)

-- | The frozen semantics: every gate enforced. All production callers use this.
fullConfig :: CheckConfig
fullConfig = CheckConfig True True True

-- | Ablation: no critical-question obligation gate.
noCQConfig :: CheckConfig
noCQConfig = fullConfig{ccObligationGate = False}

-- | Ablation: no typed-attack bundle — the paper's \"nodes and arbitrary attack
-- edges\" baseline, which neither types a declared edge nor requires a needed
-- one. It drops BOTH flags of the bundle: splitting 'ccConflictScan' out
-- added a way to switch the scan alone, and deliberately did not redefine this
-- baseline, whose measured cells are published.
noTypedConfig :: CheckConfig
noTypedConfig = fullConfig{ccTypedAttacks = False, ccConflictScan = False}

-- | Ablation: typed attacks still checked, completeness not required.
-- The isolating cell for attack completeness: the only difference from
-- 'fullConfig' is the scan, so a row that flips under it and under nothing else
-- is evidence the scan alone is load-bearing.
noConflictScanConfig :: CheckConfig
noConflictScanConfig = fullConfig{ccConflictScan = False}

-- ---------------------------------------------------------------------------
-- The checked argument cache and the attack pass
-- ---------------------------------------------------------------------------

-- | Check every argument in declaration order, retaining the completed
-- support-check result for each (Lean @checkArguments@). Rejects on the first
-- support error ('PERejection') or — when 'ccObligationGate' is on — the first
-- argument with open obligations ('PEIncompleteArgument').
checkArguments
  :: CheckConfig
  -> (RuleId -> Maybe Rule)
  -> (LeafId -> Maybe Prop)
  -> CertOk
  -> [SupportTerm]
  -> Either ProgramError [(SupportTerm, SupportResult)]
checkArguments cfg pI gamma certOk = go 0
  where
    go _ [] = Right []
    go i (w : ws) = case inferSupport pI gamma certOk LocRoot w of
      Left e -> Left (PERejection (DLArgument i) e)
      Right result -> case srObligations result of
        obs@(_ : _)
          | ccObligationGate cfg -> Left (PEIncompleteArgument i obs)
        -- gate off: retain the argument despite open obligations
        _ -> do
          rest <- go (i + 1) ws
          pure ((w, result) : rest)

-- | Check every typed attack in declaration order (Lean @checkAttacks@): both
-- endpoints must be declared arguments (R1), then — when 'ccTypedAttacks' is on
-- — the attack must type.
checkAttacks
  :: CheckConfig
  -> (RuleId -> Maybe Rule)
  -> (LeafId -> Maybe Prop)
  -> CertOk
  -> DefeatPolicy
  -> [SupportTerm]
  -> [RAttack]
  -> Either ProgramError ()
checkAttacks cfg pI gamma certOk dp args = go 0
  where
    go _ [] = Right ()
    go i (k : ks)
      | rSource k `notElem` args =
          Left (PERejection (DLAttack i) (CE_R1 LocRoot (UndeclaredAttackSource (rSource k))))
      | rTarget k `notElem` args =
          Left (PERejection (DLAttack i) (CE_R1 LocRoot (UndeclaredAttackTarget (rTarget k))))
      | not (ccTypedAttacks cfg) = go (i + 1) ks
      | otherwise = case checkAttack pI gamma certOk dp k of
          Left e -> Left (PERejection (DLAttack i) e)
          Right () -> go (i + 1) ks

-- ---------------------------------------------------------------------------
-- The indexed conflict scan (Lean @conflictCache@ / @firstMissingConflictInfo?@)
-- ---------------------------------------------------------------------------

-- | One immutable entry of the completeness scan (Lean @ConflictNode@):
-- conclusion and attackability from the retained cache, plus the bucket of
-- attacks sourced at this term.
data ConflictNode = ConflictNode
  { cnfIndex :: Int
  , cnfTerm :: SupportTerm
  , cnfConclusion :: Prop
  , cnfAttackable :: Bool
  , cnfAttacks :: [RAttack]
  }
  deriving (Eq, Show)

-- | Derive the scan cache in declaration order (Lean @conflictCache@).
conflictCache :: (RuleId -> Maybe Rule) -> [RAttack] -> [CheckedNode] -> [ConflictNode]
conflictCache pI atts nodes =
  [ ConflictNode
      i
      (cnTerm node)
      (cnConclusion node)
      (conflictAttackableB pI (cnTerm node))
      (filter (\k -> rSource k == cnTerm node) atts)
  | (node, i) <- zip nodes [0 ..]
  ]

-- | Source-major, target-major search for the first uncovered attackable
-- contrary pair (Lean @firstMissingConflictInfo?@). Ordered self-pairs are included.
firstMissingConflictInfo :: DefeatPolicy -> [ConflictNode] -> Maybe MissingConflictInfo
firstMissingConflictInfo dp cache =
  firstJust [firstJust [pairCheck s t | t <- cache] | s <- cache]
  where
    pairCheck s t
      | contraryMatchB' (cnfConclusion s) (cnfConclusion t) =
          if cnfAttackable t
            then
              if coveredB (cnfAttacks s) (cnfTerm s) (cnfTerm t)
                then Nothing
                else
                  Just
                    ( MissingConflictInfo
                        (cnfIndex s)
                        (cnfIndex t)
                        (cnfConclusion s)
                        (cnfConclusion t)
                    )
            else Nothing
      | otherwise = Nothing
    contraryMatchB' = contraryMatchB (dpContraries dp)

firstJust :: [Maybe a] -> Maybe a
firstJust = foldr (\m acc -> maybe acc Just m) Nothing

-- ---------------------------------------------------------------------------
-- The detailed program checker (Lean @checkProgramDetailed@)
-- ---------------------------------------------------------------------------

-- | Successful detailed-checker result (Lean @ProgramAcceptance@): the compiled
-- program plus the retained checked nodes (@nodes.map term = program.args@).
data ProgramAcceptance = ProgramAcceptance
  { paProgram :: CheckedProgram
  , paNodes :: [CheckedNode]
  }
  deriving (Eq, Show)

-- | Stages 4–7: duplicate arguments, support, typed attacks, missing conflict
-- (Lean @checkProgramDetailed@ = @checkProgramBase@ then the conflict scan).
-- The conflict scan is skipped when 'ccConflictScan' is off.
checkProgramDetailed
  :: CheckConfig
  -> (RuleId -> Maybe Rule)
  -> (LeafId -> Maybe Prop)
  -> CertOk
  -> DefeatPolicy
  -> [SupportTerm]
  -> [RAttack]
  -> Either ProgramError ProgramAcceptance
checkProgramDetailed cfg pI gamma certOk dp args atts =
  case firstDuplicate args of
    Just (i, j) -> Left (PEDuplicateArgument i j)
    Nothing -> do
      cache <- checkArguments cfg pI gamma certOk args
      checkAttacks cfg pI gamma certOk dp args atts
      let nodes = [CheckedNode w (srConclusion res) | (w, res) <- cache]
          missing
            | ccConflictScan cfg = firstMissingConflictInfo dp (conflictCache pI atts nodes)
            | otherwise = Nothing
      case missing of
        Just m -> Left (PEMissingConflict m)
        Nothing ->
          Right (ProgramAcceptance (CheckedProgram args atts) nodes)

-- ---------------------------------------------------------------------------
-- Attack resolution and the public boundary (Lean @Check.Unit.checkUnit@)
-- ---------------------------------------------------------------------------

-- | Resolve id-based wire attacks to term-based attacks against the unit's
-- declared arguments (the id→term half of the decode-boundary resolution both
-- drivers perform; see 'Lara.AST.Unit').
--
-- __Precondition (R14).__ Every attack endpoint must name a declared argument.
-- Under R14 each 'lookup' succeeds, so the 'mapMaybe' drops nothing: it is the
-- total id→term map, not a lenient filter that silently discards ill-formed
-- attacks. Both sanctioned 'Unit' producers discharge R14 up front:
-- 'Lara.Wire.decodeUnit' rejects a dangling endpoint as an R14 codec error, and
-- 'Lara.Elaborate.elaborate' rejects it as an elaboration error. Thus every
-- admitted unit satisfies the precondition —
-- this is the exact Haskell counterpart of the Lean driver's @resolveAttacks@
-- (@Except String@). A 'Unit' that violates R14 is outside the 'checkUnit'
-- contract below; in Lean such a unit is unrepresentable, since @Lara.Unit@
-- stores resolved @atts : List RAttack@. R14 is never a checker verdict, so a
-- dangling endpoint is caught at the boundary and never surfaced as a
-- 'UnitError' here.
resolveAttacks :: [(ArgId, SupportTerm)] -> [Attack] -> [RAttack]
resolveAttacks argMap = mapMaybe resolve
  where
    resolve k = case k of
      Rebut w u -> RRebut <$> lookup w argMap <*> lookup u argMap
      Undercut w u pos -> (\s t -> RUndercut s t pos) <$> lookup w argMap <*> lookup u argMap
      Undermine w u pos -> (\s t -> RUndermine s t pos) <$> lookup w argMap <*> lookup u argMap

-- | The canonical executable acceptance boundary (Lean @checkUnit@): the seven
-- stages in fixed order. @Gamma@ is the leaf context, @certOk@ the certificate
-- oracle (both built at the program boundary from the unit's leaves and
-- theories).
--
-- __Input contract (decoded units only).__ @unit@ must satisfy wire
-- well-formedness R14 — unique argument ids and every attack endpoint declared —
-- the guarantee every 'Unit' from 'Lara.Wire.decodeUnit' carries. R14 is a
-- codec invariant, never a checker verdict (see 'Lara.AST.RejectClass'), so it
-- is not rechecked here and has no 'UnitError'; the id→term step is delegated to
-- 'resolveAttacks', which is total under R14. A caller that forges a 'Unit'
-- bypassing the decoder owns this precondition — a dangling endpoint would be
-- dropped rather than reported, matching the Lean boundary where @Unit.atts@ is
-- already resolved.
checkUnit
  :: (LeafId -> Maybe Prop)
  -> CertOk
  -> Unit
  -> Either UnitError CheckedUnit
checkUnit = checkUnitWith fullConfig

-- | 'checkUnit' under an explicit 'CheckConfig'. The ablation entry point:
-- @checkUnitWith fullConfig = checkUnit@ definitionally, and the input contract
-- above applies verbatim.
checkUnitWith
  :: CheckConfig
  -> (LeafId -> Maybe Prop)
  -> CertOk
  -> Unit
  -> Either UnitError CheckedUnit
checkUnitWith cfg gamma certOk unit =
  case firstDuplicateRuleId (unitRules unit) of
    Just dup -> Left (UEDuplicateRule dup)
    Nothing -> case unitSortError unit of
      Just se -> Left (UESignature se)
      Nothing ->
        case firstViolation (unitRules unit) (unitContraries unit) (unitExceptions unit) of
          Just v -> Left (UEPolicyViolation v)
          Nothing ->
            let pI = lookupRule (unitRules unit)
                dp = DefeatPolicy (unitContraries unit) (unitExceptions unit)
                args = map snd (unitArgs unit)
                atts = resolveAttacks (unitArgs unit) (unitAttacks unit)
             in case checkProgramDetailed cfg pI gamma certOk dp args atts of
                  Left e -> Left (UEProgram e)
                  Right acc -> Right (CheckedUnit (paProgram acc) (paNodes acc))
