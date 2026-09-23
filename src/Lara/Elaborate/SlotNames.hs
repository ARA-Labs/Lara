-- | The authored spelling of a rule instance's premise slots.
--
-- When a registered backend refuses a certificate, the rejection is phrased
-- over premise /slots/ — @(prem 0)@, @(prem 1)@ — because that is the only
-- vocabulary the seam has ("Lara.Strict": the backend receives a positional
-- list of premise conclusions and nothing else). The author, on the @.lara@
-- door, wrote none of those indices: since @lara-syntax\@0.6@ they write leaf
-- and prior-argument names, and since @\@0.8@ premise labels. This module
-- recovers the spelling they used, so the diagnosis can be read in the same
-- vocabulary as the source.
--
-- == Why this can be derived rather than threaded
--
-- Premise resolution stores exactly what a name resolves to
-- ("Lara.Elaborate.Internal".@resolvePremises@): a leaf premise is
-- @'SLeaf' l@, and a prior-argument premise is that argument's __own
-- elaborated term__. Both readings are therefore recoverable from the
-- elaborated argument list by the same term equality
-- @certSlotResolver@ already locates by — no name map has to be threaded out
-- of the recursive elaborator, and no value has to reach 'Unit'.
--
-- == Why it stops at the source door
--
-- These names exist only where a surface was authored. A raw @.sexp@ input
-- never had them, and 'Lara.AST.rulePremiseLabels' is stripped on the way into
-- 'Unit' (grammar App. B.4, \"labels never enter @Unit@\"). The structural
-- reading that both doors always have is
-- 'Lara.SupportTerm.SlotSource'; this is the enrichment layered over it on the
-- @.lara@ door only.
module Lara.Elaborate.SlotNames
  ( AuthoredReferent (..)
  , AuthoredSlot (..)
  , authoredSlotMap
  , renderAuthoredSlots
  ) where

import Data.List (find)

import Lara.AST

-- | What the author named in one premise slot.
data AuthoredReferent
  = -- | a declared leaf, by its source id
    ARLeaf LeafId
  | -- | a prior argument, by its source id
    ARArg ArgId
  | -- | neither: an inline sub-derivation with no authored name of its own,
    -- reported by the rule that concluded it (the structural reading)
    ARDerived RuleId
  deriving (Eq, Show)

-- | One premise slot's authored spelling: what fills it, plus the label the
-- citing rule declares for that slot when it declares one (@lara-syntax\@0.8@).
--
-- The label is carried even though the referent alone usually identifies the
-- slot, because it is the __only__ spelling that discriminates the multi-slot
-- case: when one leaf feeds two premises, both slots print the same referent
-- and only the labels differ (the case @certSlotResolver@ rejects as
-- @SlotNameMultiSlot@).
data AuthoredSlot = AuthoredSlot
  { asReferent :: AuthoredReferent
  , asLabel :: Maybe PremiseLabel
  }
  deriving (Eq, Show)

-- | The authored slot spelling of every elaborated argument, keyed by argument
-- id.
--
-- Keyed by id rather than position because a policy-pruned program indexes its
-- /checked/ arguments, and resolving a rejection's constituent index against
-- the declared list would misattribute every argument after a pruned one (the
-- same reason 'Lara.Elaborate.sourceResultCheckedArgIds' exists).
--
-- An argument whose term is a bare leaf has no premise slots and is omitted.
authoredSlotMap :: Policy -> [(ArgId, SupportTerm)] -> [(ArgId, [AuthoredSlot])]
authoredSlotMap pol args =
  [ (aid, slotsOf rn prems)
  | (aid, SRule{srRule = rn, srPremises = prems}) <- args
  ]
  where
    slotsOf rn prems =
      [ AuthoredSlot (referentOf p) (labelAt rn i)
      | (i, p) <- zip [0 ..] prems
      ]

    -- A leaf premise names its leaf; anything else is a prior argument's own
    -- elaborated term, so it is found by the term equality premise resolution
    -- stored it under. An unnamed inline sub-derivation falls back to the
    -- structural reading.
    --
    -- The match must be __unique__ to name an argument. 'SupportTerm' equality
    -- is fully structural and carries no identity, so nothing about the /term/
    -- rules out two arguments sharing one. What rules it out is the checker:
    -- @Lara.Check.firstDuplicate@ rejects a unit with two structurally
    -- identical argument terms outright (@duplicate-argument@), and it scans
    -- exactly the list this map is keyed over — the checked unit's arguments.
    -- A unit that reaches a @StageSupport@ rejection therefore has pairwise
    -- distinct argument terms, and at most one match exists.
    --
    -- Matching on the singleton list rather than taking @find@'s first hit
    -- makes that invariant load-bearing in the code instead of in a comment: if
    -- the dedupe is ever relaxed, this degrades to the structural reading
    -- rather than printing a confident and possibly wrong id, which is the one
    -- failure this block exists to prevent.
    referentOf p = case p of
      SLeaf l -> ARLeaf l
      SRule{srRule = rn} -> case filter ((== p) . snd) args of
        [(aid, _)] -> ARArg aid
        _ -> ARDerived rn

    labelAt rn i = case find ((== rn) . ruleId) (policyRules pol) of
      Nothing -> Nothing
      Just rule -> case drop i (rulePremiseLabels rule) of
        lbl : _ -> lbl
        [] -> Nothing

-- | Render an authored slot mapping as one @stderr@ line per slot, in the
-- shape 'Lara.Driver.slotMappingLines' uses for the structural reading.
--
-- Referents are padded to a common width so the labels line up: a multi-slot
-- rejection is read by scanning the column, not the sentence.
--
-- Padding is what a label is aligned /against/, so only a slot that carries one
-- is padded. A rule may label some premises and not others (grammar App. B.4),
-- and padding those unlabelled lines would append trailing whitespace no reader
-- can see to bytes this project pins exactly.
renderAuthoredSlots :: [AuthoredSlot] -> [String]
renderAuthoredSlots slots =
  [ "  slot " ++ show i ++ " = " ++ pad s (renderReferent (asReferent s)) ++ label s
  | (i, s) <- zip [0 :: Int ..] slots
  ]
  where
    width = maximum (0 : map (length . renderReferent . asReferent) slots)
    pad s t = case asLabel s of
      Nothing -> t
      Just _ -> t ++ replicate (width - length t) ' '
    label s = case asLabel s of
      Nothing -> ""
      Just (PremiseLabel l) -> "  [label: " ++ l ++ "]"

-- | The authored spelling of one slot's source.
renderReferent :: AuthoredReferent -> String
renderReferent r = case r of
  ARLeaf (LeafId l) -> "leaf " ++ l
  ARArg (ArgId a) -> "arg " ++ a
  ARDerived (RuleId rn) -> "derived by " ++ rn
