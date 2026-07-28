-- | Full claim holes and incomplete-alternative diagnostics (spec §8, N17
-- point 1) — the reporting surface deferred past the complete-only
-- 'Lara.Grounded.completeClaimFor' projection.
--
-- Spec §8 defines two per-claim sets. @support(P,p)@ is the /complete/ checked
-- support arguments for @p@ (obligation set @{}@, AF-eligible) — computed by
-- 'Lara.Grounded.claimSupportFor' and reused verbatim here. @holes(P,p)@ is the
-- /unresolved root obligations/ of @p@'s /incomplete/ candidate alternatives:
-- support terms that would support @p@ but carry an open mandatory critical
-- question (spec §6.1), so they are excluded from the AF and never reach an
-- accepted 'Lara.Check.CheckedUnit'.
--
-- Because 'Lara.Check.checkArguments' /rejects/ the whole unit on the first
-- incomplete argument ('Lara.Check.PEIncompleteArgument'), the incomplete
-- alternatives are invisible to the accept path. This module therefore runs a
-- separate __lenient__ scan over the raw 'Unit' arguments: it records each
-- incomplete alternative (located by its raw-argument index) instead of
-- rejecting, and it never touches the driver's verdict wire output.
--
-- __Status priority (N17 point 1, resolved).__ A hole forces @gap@ only when
-- @support(P,p)@ is empty. 'Lara.Grounded.statusC' already realizes this: it
-- decides @gap@ on empty complete support alone and never reads 'claimHoles', so
-- a complete winning @in@ argument is never downgraded by a hole on some other
-- alternative. Holes instead surface through the separate
-- 'incompleteAlternative' diagnostic (Lean @incompleteAlternative@). "Status
-- never hides holes, but a winning complete argument is not suppressed by them."
--
-- __Hole index convention.__ 'holesFor' populates 'Lara.Grounded.claimHoles'
-- with the /declaration-order index of each incomplete alternative in the raw
-- unit's @unitArgs@/ (the 'iaIndex' of a located 'IncompleteAlternative') — a
-- stable, locatable identity that lets a consumer join a hole back to its term
-- and open obligations. This is a /different/ index space from 'claimSupport',
-- whose entries are complete-node (AF) indices; the two never interact
-- numerically, because 'statusC' reads only 'claimSupport' for the status and
-- only the /nonemptiness/ of 'claimHoles' feeds the diagnostic.
module Lara.Reporting
  ( -- * Located incomplete alternatives (spec §6.1 open root obligations)
    IncompleteAlternative (..)
  , scanArguments
  , incompleteAlternativesFor
    -- * Holes and the full reporting claim (spec §8)
  , holesFor
  , reportClaimFor
  , incompleteAlternative
    -- * The reporting AF and per-query reports
  , reportAF
  , ClaimReport (..)
  , claimReports
  ) where

import Lara.AST hiding (Claim)
import Lara.Check (resolveAttacks)
import Lara.Compile (checkedAF)
import Lara.Compile.Internal (CheckedProgram (..))
import Lara.Grounded
  ( AF
  , Claim (..)
  , claimSupportFor
  , statusC
  )
import Lara.Prop (Prop, equiv)
import Lara.SupportTerm
  ( CertOk
  , CheckLoc (LocRoot)
  , SupportResult (..)
  , inferSupport
  )
import Lara.SupportTerm.Internal (CheckedNode (..))

-- ---------------------------------------------------------------------------
-- Located incomplete alternatives
-- ---------------------------------------------------------------------------

-- | A candidate support term retained by lenient reporting: a raw argument that
-- type-checks but carries open root obligations (unmet mandatory critical
-- questions, spec §6.1), so it is excluded from the AF. Located by its
-- declaration-order index in the raw unit's @unitArgs@.
data IncompleteAlternative = IncompleteAlternative
  { iaIndex :: Int -- ^ declaration-order index in @unitArgs@
  , iaArgId :: ArgId
  , iaTerm :: SupportTerm
  , iaConclusion :: Prop
  , iaObligations :: [QuestionId] -- ^ unresolved root obligations (nonempty)
  }
  deriving (Eq, Show)

-- | Leniently check every declared argument, partitioning into complete checked
-- nodes (obligation set @[]@, AF-eligible) and located incomplete alternatives
-- (obligation set nonempty, AF-excluded). A hard type error (a 'Left' from
-- 'inferSupport') is dropped: it is neither complete support nor a hole. Unlike
-- 'Lara.Check.checkArguments', this never rejects — every argument is scanned.
--
-- The retained nodes are in declaration order, so their positions are exactly
-- the AF indices 'reportAF' compiles them into.
scanArguments
  :: (RuleId -> Maybe Rule)
  -> (LeafId -> Maybe Prop)
  -> CertOk
  -> [(ArgId, SupportTerm)]
  -> ([CheckedNode], [IncompleteAlternative])
scanArguments pI gamma certOk = go 0
  where
    go _ [] = ([], [])
    go i ((aid, w) : rest) =
      let (nodes, alts) = go (i + 1) rest
       in case inferSupport pI gamma certOk LocRoot w of
            Left _ -> (nodes, alts)
            Right res
              | null (srObligations res) ->
                  (CheckedNode w (srConclusion res) : nodes, alts)
              | otherwise ->
                  ( nodes
                  , IncompleteAlternative i aid w (srConclusion res) (srObligations res)
                      : alts
                  )

-- | The located incomplete alternatives whose conclusion is @≡ p@ (spec §8's
-- incomplete candidate alternatives for @p@).
incompleteAlternativesFor :: [IncompleteAlternative] -> Prop -> [IncompleteAlternative]
incompleteAlternativesFor alts p = [a | a <- alts, equiv (iaConclusion a) p]

-- ---------------------------------------------------------------------------
-- Holes and the full reporting claim
-- ---------------------------------------------------------------------------

-- | @holes(P,p)@ as the @[Int]@ populating 'Lara.Grounded.claimHoles': the
-- raw-unit indices ('iaIndex') of the incomplete alternatives whose conclusion
-- is @≡ p@. Nonempty exactly when @p@ has an incomplete candidate alternative.
--
-- These are @unitArgs@ declaration indices — a __different index space__ from
-- 'Lara.Grounded.claimSupport' (complete-node/AF indices), sharing the @[Int]@
-- type only because the Lean @Claim@ mirror keeps both as @List Arg@. Only their
-- (non)emptiness is ever consumed (by 'incompleteAlternative'); a consumer that
-- must resolve a hole back to its term or open obligations reads the located
-- 'IncompleteAlternative' values ('crAlternatives' \/ 'incompleteAlternativesFor'),
-- and must never treat these ints as AF indices.
holesFor :: [IncompleteAlternative] -> Prop -> [Int]
holesFor alts p = [iaIndex a | a <- alts, equiv (iaConclusion a) p]

-- | The /full/ reporting claim for @p@: complete support indices reused from
-- 'claimSupportFor' (identical to 'Lara.Grounded.completeClaimFor''s support)
-- plus the located hole indices. This is deliberately __distinct__ from
-- 'Lara.Grounded.completeClaimFor', whose 'claimHoles' is always @[]@: the
-- complete-only projection and the full reporting path are never conflated
-- (plan D3/Step 5).
reportClaimFor :: [CheckedNode] -> [IncompleteAlternative] -> Prop -> Claim
reportClaimFor nodes alts p =
  Claim
    { claimSupport = claimSupportFor nodes p
    , claimHoles = holesFor alts p
    }

-- | The @incompleteAlternative@ diagnostic (Lean
-- @incompleteAlternative (c) := decide (c.holes ≠ [])@): fires exactly when the
-- claim carries a hole. 'statusC' never reads it by construction, so it neither
-- suppresses nor is suppressed by a complete winning argument.
incompleteAlternative :: Claim -> Bool
incompleteAlternative c = not (null (claimHoles c))

-- ---------------------------------------------------------------------------
-- The reporting AF and per-query reports
-- ---------------------------------------------------------------------------

-- | The reporting AF, built from the complete nodes only — the incomplete
-- alternatives are excluded (spec §8). Attacks are resolved against the whole
-- raw argument list, but 'Lara.Compile.edgeB' only forms an edge between two
-- complete terms, so an attack sourced at or targeting an excluded incomplete
-- term contributes no edge.
reportAF :: [(ArgId, SupportTerm)] -> [Attack] -> [CheckedNode] -> AF
reportAF rawArgs attacks nodes =
  checkedAF (CheckedProgram (map cnTerm nodes) (resolveAttacks rawArgs attacks))

-- | One claim's full reporting record (spec §8): the query atom, the full claim
-- (complete support indices + hole indices), its four-state status, the located
-- incomplete alternatives, and the 'incompleteAlternative' diagnostic.
data ClaimReport = ClaimReport
  { crQuery :: Prop
  , crClaim :: Claim
  , crStatus :: Status
  , crAlternatives :: [IncompleteAlternative]
  , crIncompleteAlternative :: Bool
  }
  deriving (Eq, Show)

-- | The full reporting analysis for a raw unit: a lenient argument scan, an AF
-- over the complete nodes, and one 'ClaimReport' per query atom. This is a
-- library/API surface only — it does not feed the driver verdict, so the frozen
-- fixture wire output is unaffected.
claimReports
  :: (RuleId -> Maybe Rule)
  -> (LeafId -> Maybe Prop)
  -> CertOk
  -> Unit
  -> [ClaimReport]
claimReports pI gamma certOk unit =
  [ let claim = reportClaimFor nodes alts p
     in ClaimReport
          { crQuery = p
          , crClaim = claim
          , crStatus = statusC af claim
          , crAlternatives = incompleteAlternativesFor alts p
          , crIncompleteAlternative = incompleteAlternative claim
          }
  | p <- unitQueries unit
  ]
  where
    (nodes, alts) = scanArguments pI gamma certOk (unitArgs unit)
    af = reportAF (unitArgs unit) (unitAttacks unit) nodes
