-- | Full claim holes and incomplete-alternative diagnostics (spec §8, N17
-- point 1) — the reporting surface beside the complete-only
-- 'Lara.Grounded.completeClaimFor' projection.
--
-- Spec §8 defines two per-claim sets. @support(P,p)@ is the /complete/ checked
-- support arguments for @p@ (obligation set @{}@, AF-eligible) — computed by
-- 'Lara.Grounded.claimSupportFor' and reused verbatim here. @holes(P,p)@ is the
-- /unresolved root obligations/ of @p@'s /incomplete/ candidate alternatives:
-- support terms that type but carry an open mandatory critical question
-- (spec §6.1), so they are excluded from the AF.
--
-- Since @lara-core\@0.3@ the checker accepts such a unit and partitions its
-- argument cache once into AF nodes and located holes
-- ('Lara.Check.cuNodes' \/ 'Lara.Check.cuHoles', spec §4.4). This module reads
-- that partition and the compiled program of the __accepted__ unit; it runs no
-- support inference and builds no second graph. A claim report exists only for
-- an accepted unit.
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
-- with the /checked declaration index/ of each incomplete alternative — its
-- position in the unit 'Lara.Check.checkUnit' accepted ('iaIndex', the
-- checker's 'Lara.SupportTerm.chIndex'). This is a /different/ index space from
-- 'claimSupport', whose entries are AF indices, and from the original
-- declaration index a driver reports after admission; the two never interact
-- numerically, because 'statusC' reads only 'claimSupport' for the status and
-- only the /nonemptiness/ of 'claimHoles' feeds the diagnostic.
module Lara.Reporting
  ( -- * Located incomplete alternatives (spec §4.4 located holes)
    IncompleteAlternative (..)
  , locatedHoles
  , incompleteAlternativesFor
    -- * Holes and the full reporting claim (spec §8)
  , holesFor
  , reportClaimFor
  , incompleteAlternative
    -- * Per-query reports
  , ClaimReport (..)
  , claimReports
    -- * Naming AF nodes
  , nodeArgIds
  ) where

import Lara.AST hiding (Claim)
import Lara.Check (CheckedUnit, cuHoles, cuNodeDecls, cuNodes, cuProgram)
import Lara.Compile (checkedAF)
import Lara.Grounded
  ( Claim (..)
  , claimSupportFor
  , statusC
  )
import Lara.Prop (Prop, equiv)
import Lara.SupportTerm
  ( CheckedNode
  , chConclusion
  , chIndex
  , chObligations
  , chTerm
  )

-- ---------------------------------------------------------------------------
-- Located incomplete alternatives
-- ---------------------------------------------------------------------------

-- | One located hole of an accepted unit, as reporting names it: the checker's
-- 'Lara.SupportTerm.CheckedHole' plus the 'ArgId' the checked unit declares at
-- its index. It type-checks but carries open mandatory root obligations
-- (spec §6.1), so it is excluded from the AF.
data IncompleteAlternative = IncompleteAlternative
  { iaIndex :: Int -- ^ checked declaration index ('Lara.SupportTerm.chIndex')
  , iaArgId :: ArgId
  , iaTerm :: SupportTerm
  , iaConclusion :: Prop
  , iaObligations :: [QuestionId] -- ^ exact mandatory root obligations (nonempty)
  }
  deriving (Eq, Show)

-- | The located holes of an accepted unit, in checked declaration order, named
-- by the argument ids of @unit@.
--
-- __Input contract.__ @unit@ is the unit 'Lara.Check.checkUnit' accepted as
-- @accepted@ — after any §4.3 prune, so the hole indices address its argument
-- list. A hole index outside that list means the two were not paired by one
-- check; that is a caller bug, and it fails loudly rather than name a hole by
-- some other argument's id.
locatedHoles :: Unit -> CheckedUnit -> [IncompleteAlternative]
locatedHoles unit accepted =
  [ IncompleteAlternative
      (chIndex hole)
      (argIdAt (chIndex hole))
      (chTerm hole)
      (chConclusion hole)
      (chObligations hole)
  | hole <- cuHoles accepted
  ]
  where
    argIds = zip [0 :: Int ..] (map fst (unitArgs unit))
    argIdAt i = case lookup i argIds of
      Just aid -> aid
      Nothing ->
        error
          ( "Lara.Reporting.locatedHoles: hole at checked index "
              ++ show i
              ++ " is outside the supplied unit"
          )

-- | The located incomplete alternatives whose conclusion is @≡ p@ (spec §8's
-- incomplete candidate alternatives for @p@).
incompleteAlternativesFor :: [IncompleteAlternative] -> Prop -> [IncompleteAlternative]
incompleteAlternativesFor alts p = [a | a <- alts, equiv (iaConclusion a) p]

-- ---------------------------------------------------------------------------
-- Holes and the full reporting claim
-- ---------------------------------------------------------------------------

-- | @holes(P,p)@ as the @[Int]@ populating 'Lara.Grounded.claimHoles': the
-- checked declaration indices ('iaIndex') of the incomplete alternatives whose
-- conclusion is @≡ p@. Nonempty exactly when @p@ has an incomplete candidate
-- alternative.
--
-- These are checked declaration indices — a __different index space__ from
-- 'Lara.Grounded.claimSupport' (AF indices), sharing the @[Int]@ type only
-- because the Lean @Claim@ mirror keeps both as @List Arg@. Only their
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
-- Per-query reports
-- ---------------------------------------------------------------------------

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

-- | The full reporting analysis of an accepted unit: one 'ClaimReport' per
-- query atom of @unit@, over the checker's own node cache, located holes and
-- compiled AF ('Lara.Compile.checkedAF' of 'Lara.Check.cuProgram'). The input
-- contract is 'locatedHoles''s: @unit@ is the unit the checker accepted.
--
-- The status is the four-state 'statusC' of the checked graph. It is not a
-- public status: §4.3's @evidence-blocked@ overlay is the driver's
-- ('Lara.Driver.buildAccept'), and a caller that publishes a status reads it
-- from the verdict.
claimReports :: Unit -> CheckedUnit -> [ClaimReport]
claimReports unit accepted =
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
    nodes = cuNodes accepted
    alts = locatedHoles unit accepted
    af = checkedAF (cuProgram accepted)

-- ---------------------------------------------------------------------------
-- Naming AF nodes
-- ---------------------------------------------------------------------------

-- | The argument id of every AF node of an accepted unit, in AF order: entry
-- @n@ names the label and edge index @n@. AF node @n@ is checked declaration
-- @'Lara.Check.cuNodeDecls' !! n@, which differs from @n@ as soon as a hole
-- precedes it, so a consumer naming labels must go through this map rather
-- than index the declaration list with an AF index. The input contract is
-- 'locatedHoles''s.
nodeArgIds :: Unit -> CheckedUnit -> [ArgId]
nodeArgIds unit accepted =
  [ case lookup d argIds of
      Just aid -> aid
      Nothing ->
        error
          ( "Lara.Reporting.nodeArgIds: node at checked index "
              ++ show d
              ++ " is outside the supplied unit"
          )
  | d <- cuNodeDecls accepted
  ]
  where
    argIds = zip [0 :: Int ..] (map fst (unitArgs unit))
