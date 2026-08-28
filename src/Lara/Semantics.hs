-- | Dung extension semantics over a compiled framework — the Haskell mirror of
-- the enumeration half of @lean\/Lara\/Semantics.lean@ and of
-- @lean\/Lara\/Semantics\/Sublists.lean@ (@subseqs@).
--
-- __What this module is, and is not.__ It mirrors the /executable/ layer of the
-- Lean development: the powerset scan 'subseqs', the @Bool@ deciders, and the
-- five @enumerate@ functions. The Lean module's @Prop@ layer (@Bounded@,
-- @Admissible@, @Complete@, @Stable@, @LeastComplete@, @Preferred@,
-- @SemiStable@) and the adequacy theorems tying each @Prop@ to its decider
-- (@admissibleB_iff@ and friends) have no Haskell counterpart and are not
-- reproduced here: they are the part that carries soundness, and it stays in
-- Lean. Likewise the @ExtensionSemantics@ record is not mirrored, because its
-- content is the bundled @sound@ field; without it the record would be a
-- five-element enum of functions dressed up as the Lean interface.
--
-- __Status of the correspondence.__ The definitions below were written against
-- the Lean source declaration by declaration, and @test\/SemanticsSpec.hs@
-- checks that all five enumerations agree with Lean-derived golden values on
-- the six observation-table frameworks of
-- @lean\/Lara\/Examples\/Semantics.lean@. That is agreement of /outputs on six
-- frameworks/, not a proof that the definitions correspond. Per @CLAUDE.md@:
-- Haskell property tests are conformance evidence, not soundness; the Lean
-- proofs carry soundness.
--
-- __Performance disclaimer, restated from the Lean header.__
-- 'candidates' is a powerset scan, so it is exponential in @length (afArgs f)@,
-- and 'preferredB' \/ 'semiStableB' \/ 'leastCompleteB' scan that list once per
-- candidate. Nothing here is a proposed runtime. The runtime evaluator stays
-- grounded: 'Lara.Grounded.grounded' is the total, deterministic, polynomial
-- fixed-point computation, and it is what the verdict path reaches, through
-- 'Lara.Grounded.labelC' and 'Lara.Grounded.statusC' (their only callers in the
-- library are "Lara.Driver.Internal" and "Lara.Reporting"). These enumerations
-- exist to give the non-grounded semantics a meaning that small examples can
-- exercise.
--
-- __The carrier bound is inside the predicates, not the quantifiers.__
-- 'Lara.Grounded.defendedB' only scans attackers that lie inside 'afArgs', so an
-- argument outside the carrier that no carrier member attacks is vacuously
-- defended by everything. 'boundedB' is therefore a conjunct of 'admissibleB'
-- and 'stableB', exactly as in Lean, and that placement is load-bearing rather
-- than incidental.
--
-- __Representation.__ An extension is an order-preserving subsequence of
-- 'afArgs', not an arbitrary list. When 'afArgs' is duplicate-free each subset
-- of the carrier has exactly one representative, so the enumeration is a
-- faithful powerset; that is Lean @subseqs_ext@ \/ @subseqs_nodup@, which are
-- theorems there and assumptions here.
module Lara.Semantics
  ( -- * Candidate extensions (Lean @subseqs@ \/ @candidates@)
    subseqs
  , candidates
    -- * Containment and the carrier bound
  , subB
  , boundedB
    -- * The extension deciders
  , conflictFreeB
  , admissibleB
  , completeB
  , stableB
  , leastCompleteB
  , preferredB
    -- * Range, and the semi-stable decider
  , attacked
  , reach
  , semiStableB
    -- * The five enumerations (Lean @ExtensionSemantics.enumerate@)
  , enumerateGrounded
  , enumerateComplete
  , enumeratePreferred
  , enumerateStable
  , enumerateSemiStable
  ) where

import Lara.Grounded (AF (..), defendedB)

-- ---------------------------------------------------------------------------
-- Candidate extensions
-- ---------------------------------------------------------------------------

-- | Order-preserving subsequences of a list (Lean
-- @Lara.Semantics.Sublists.subseqs@). For each element the recursion branches on
-- \"drop it\" \/ \"keep it\", in that order, so the emitted order matches the
-- Lean @flatMap (fun s => [s, a :: s])@ exactly — which matters, because the
-- golden values in @test\/SemanticsSpec.hs@ are compared as lists, not as sets.
subseqs :: [Int] -> [[Int]]
subseqs [] = [[]]
subseqs (a : l) = concatMap (\s -> [s, a : s]) (subseqs l)

-- | The candidate extensions of a framework: every order-preserving
-- subsequence of the carrier (Lean @candidates@). Exponential by construction —
-- see the module header.
candidates :: AF -> [[Int]]
candidates f = subseqs (afArgs f)

-- ---------------------------------------------------------------------------
-- Containment and the carrier bound
-- ---------------------------------------------------------------------------

-- | Containment as a @Bool@ (Lean @subB@). One notion used at both scales:
-- containment in the carrier ('boundedB') and containment between two
-- extensions (the maximality scans).
subB :: [Int] -> [Int] -> Bool
subB s t = all (`elem` t) s

-- | The carrier bound (Lean @boundedB@): definitionally @subB s (afArgs f)@.
-- Carrier membership is not a second notion of containment.
boundedB :: AF -> [Int] -> Bool
boundedB f s = subB s (afArgs f)

-- ---------------------------------------------------------------------------
-- The extension deciders
-- ---------------------------------------------------------------------------

-- | No member of @s@ attacks a member of @s@ (Lean @conflictFreeB@, deciding
-- @Lara.Grounded.ConflictFree@). The doubly-nested scan is the same
-- transparent-over-fast trade 'Lara.Grounded.defendedB' makes.
conflictFreeB :: AF -> [Int] -> Bool
conflictFreeB f s = all (\a -> all (\b -> not (afAttack f a b)) s) s

-- | Admissible: inside the carrier, conflict-free, and defending each of its own
-- members (Lean @admissibleB@).
admissibleB :: AF -> [Int] -> Bool
admissibleB f s =
  boundedB f s && conflictFreeB f s && all (defendedB f s) s

-- | Complete: admissible and closed under defence (Lean @completeB@).
completeB :: AF -> [Int] -> Bool
completeB f s =
  admissibleB f s
    && all (\a -> not (defendedB f s a) || a `elem` s) (afArgs f)

-- | Stable: bounded, conflict-free, and attacking every carrier argument it does
-- not contain (Lean @stableB@). Not routed through 'admissibleB': the textbook
-- definition is the attack condition, and keeping it that way leaves
-- @Stable ⇒ Admissible@ an implication to prove rather than a definitional
-- truth. (No such theorem is currently stated, on either side.)
stableB :: AF -> [Int] -> Bool
stableB f s =
  boundedB f s
    && conflictFreeB f s
    && all (\a -> a `elem` s || any (\b -> afAttack f b a) s) (afArgs f)

-- | Least complete under inclusion (Lean @leastCompleteB@) — the declarative
-- characterization @groundedSem@ uses, rather than a reference to
-- 'Lara.Grounded.grounded'. The minimality clause is scanned over 'candidates'
-- only; in Lean that restriction is justified by @exists_candidate_ext@ and
-- @complete_congr@, which are not mirrored here.
leastCompleteB :: AF -> [Int] -> Bool
leastCompleteB f s =
  completeB f s
    && all (\t -> not (completeB f t) || all (`elem` t) s) (candidates f)

-- | Preferred: admissible and inclusion-maximal among admissible sets (Lean
-- @preferredB@). Maximality is mutual containment, not list equality, for the
-- representation-independence reason spelled out in the Lean source.
preferredB :: AF -> [Int] -> Bool
preferredB f s =
  admissibleB f s
    && all
      (\t -> not (admissibleB f t && subB s t) || subB t s)
      (candidates f)

-- ---------------------------------------------------------------------------
-- Range, and the semi-stable decider
-- ---------------------------------------------------------------------------

-- | @S⁺@: the carrier arguments that @s@ attacks (Lean @attacked@). Not the
-- range — the range is @S ∪ S⁺@, which is 'reach'.
attacked :: AF -> [Int] -> [Int]
attacked f s = filter (\a -> any (\b -> afAttack f b a) s) (afArgs f)

-- | The range of @s@ in Dung's sense: @S ∪ S⁺@ (Lean @reach@). Named @reach@
-- there to avoid colliding with core @List.range@; the name is kept here so the
-- two modules can be read side by side.
reach :: AF -> [Int] -> [Int]
reach f s = s ++ attacked f s

-- | Semi-stable: complete, with inclusion-maximal 'reach' among complete
-- extensions (Lean @semiStableB@).
semiStableB :: AF -> [Int] -> Bool
semiStableB f s =
  completeB f s
    && all
      (\t ->
         not (completeB f t && subB (reach f s) (reach f t))
           || subB (reach f t) (reach f s))
      (candidates f)

-- ---------------------------------------------------------------------------
-- The five enumerations
-- ---------------------------------------------------------------------------

-- | The grounded semantics as a filter of 'candidates' (Lean
-- @groundedSem.enumerate@). Over a duplicate-free carrier Lean's
-- @groundedSem_enumerate@ proves this is a one-element list whose entry has
-- exactly the members of 'Lara.Grounded.grounded'; that is a Lean theorem, not
-- something this function establishes.
enumerateGrounded :: AF -> [[Int]]
enumerateGrounded f = filter (leastCompleteB f) (candidates f)

-- | The complete semantics (Lean @completeSem.enumerate@).
enumerateComplete :: AF -> [[Int]]
enumerateComplete f = filter (completeB f) (candidates f)

-- | The preferred semantics (Lean @preferredSem.enumerate@).
enumeratePreferred :: AF -> [[Int]]
enumeratePreferred f = filter (preferredB f) (candidates f)

-- | The stable semantics (Lean @stableSem.enumerate@). Unlike the other four
-- this one can be empty: the bare three-cycle has no stable extension (Lean
-- @stableSem_enumerate_threeCycle@, and the corresponding golden value in
-- @test\/SemanticsSpec.hs@).
enumerateStable :: AF -> [[Int]]
enumerateStable f = filter (stableB f) (candidates f)

-- | The semi-stable semantics (Lean @semiStableSem.enumerate@).
enumerateSemiStable :: AF -> [[Int]]
enumerateSemiStable f = filter (semiStableB f) (candidates f)
