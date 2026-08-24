-- | Formula attribution on an @nd\@1@ replay rejection (#148,
-- "Lara.Elaborate.FormulaNames").
--
-- The contract under test is one stderr block. When a named proof term lowers
-- cleanly and the certificate is then refused at R13, the backend's reason
-- names atoms by the opaque 'Lara.Strict.ND.encodeAtomKey' framing —
-- @FAtom (AtomId \"1:A5:holds1:L1:2…\")@ — for formulas the author wrote as
-- @(prop \"holds(safety_invariant, D)\")@ and as @leaf@ declarations. These
-- lines put the authored spelling back.
--
-- The cases that matter are the ones where the naive design would be wrong:
-- a mismatch names __two__ atoms from __two different sources__ (an annotation
-- and a leaf), the lines must follow the order the reason names them rather
-- than the order the source declares them, and an atom the source never
-- authored must contribute no line at all rather than a guess.
module FormulaNamesSpec (formulaNamesSpecProps) where

import Data.List (isInfixOf)
import Test.QuickCheck

import Lara.AST (LeafId (..), Policy, Program)
import Lara.Admission (renderAdmissionRejection)
import Lara.Elaborate
  ( PreparedSource (..)
  , prepareSource
  , renderSourceInvalid
  , runSourceCheck
  , sourceResultAuthorDiagnostics
  , sourceResultAuthoredFormulas
  )
import Lara.Elaborate.FormulaNames
  ( AuthoredFormula (..)
  , FormulaOrigin (..)
  , formulaMappingLines
  )
import Lara.Elaborate.NDNamed (authoredPropAnnotations)
import Lara.Prop (nf)
import Lara.Strict (SExpr (..))
import qualified Lara.Strict.ND as ND (encodeAtomKey)
import Lara.Syntax (parsePolicy, parseProgram, parseProp)

-- ---------------------------------------------------------------------------
-- Fixtures
-- ---------------------------------------------------------------------------

-- | The @examples\/S8@ policy: one strict rule certified by @nd\@1@ over an
-- empty theory, so every atom the backend names comes from the artifact rather
-- than from a theory entry.
s8Policy :: String
s8Policy =
  unlines
    [ "policy strict-v1"
    , "sort Property, Scope"
    , "con D : Scope"
    , "con safety_invariant : Property"
    , "con other_invariant : Property"
    , "pred holds(Property, Scope)"
    , "rule certified_citation(X, D)"
    , "  mode       = strict"
    , "  premises   = [ holds(X, D) ]"
    , "  conclusion = holds(X, D)"
    , "  allow-trusted = false"
    , "  certifiers = [ (nd@1, sha256:strict-v1-theory-0) ]"
    , "theory sha256:strict-v1-theory-0 = []"
    ]

-- | @examples\/S8@ with its named proof term's formula annotation replaced by
-- @annotation@.
--
-- The accepted spelling is @holds(safety_invariant, D)@, matching leaf @e1@.
-- Any other proposition still __lowers__ — it parses, and @(prop …)@ imposes no
-- agreement with the premise — and then fails the backend's application rule,
-- which is exactly the post-lowering R13 this module exists for.
s8ProgramWith :: String -> String
s8ProgramWith annotation =
  unlines
    [ "artifact paper_42 at sha256:bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb"
    , "policy strict-v1"
    , "use backends [nd@1]"
    , "claim c1"
    , "  nl      = \"The safety invariant holds for deployment D\""
    , "  formal  = holds(safety_invariant, D)"
    , "  binding = { author = alice, audit-status = reviewed }"
    , "leaf e1 : holds(safety_invariant, D)"
    , "  kind       = attested"
    , "  provenance = user"
    , "  refs       = [evidence/safety_audit.txt#section=invariants]"
    , "arg a1 : supports(c1) by certified_citation from [e1]"
    , "  assurance = cert(nd@1, sha256:strict-v1-theory-0, (app (lam h (prop \""
        ++ annotation
        ++ "\") (prem e1)) (prem e1)))"
    , "status c1"
    ]

-- | The rejecting artifact: the annotation names a proposition the premise does
-- not conclude, so the application mismatches and the reason names both atoms.
s8Mismatch :: String
s8Mismatch = s8ProgramWith "holds(other_invariant, D)"

-- ---------------------------------------------------------------------------
-- Drivers
-- ---------------------------------------------------------------------------

parsed :: String -> String -> Either String (Program, Policy)
parsed programSource policySource = do
  program <- either (Left . show) Right (parseProgram programSource)
  policy <- either (Left . show) Right (parsePolicy policySource)
  pure (program, policy)

-- | The author-facing stderr lines of one source artifact — what @lara check@
-- prints on the @.lara@ door.
authorLines :: String -> Either String [String]
authorLines programSource = do
  (program, policy) <- parsed programSource s8Policy
  case prepareSource program policy of
    Left invalid -> Left ("source invalid: " ++ renderSourceInvalid invalid)
    Right (SourceRejected rejection) ->
      Left ("admission rejection: " ++ renderAdmissionRejection rejection)
    Right (SourceAccepted input) ->
      Right (sourceResultAuthorDiagnostics (runSourceCheck input))

-- | The recovered map the same artifact carries, before any rendering.
authoredFormulas :: String -> Either String [AuthoredFormula]
authoredFormulas programSource = do
  (program, policy) <- parsed programSource s8Policy
  case prepareSource program policy of
    Left invalid -> Left ("source invalid: " ++ renderSourceInvalid invalid)
    Right (SourceRejected rejection) ->
      Left ("admission rejection: " ++ renderAdmissionRejection rejection)
    Right (SourceAccepted input) ->
      Right (sourceResultAuthoredFormulas (runSourceCheck input))

-- | Every line after the backend's reason and its slot block: the formula
-- block alone.
formulaBlock :: [String] -> [String]
formulaBlock = filter (\l -> take 10 l == "  formula ")

-- | The key the backend names a proposition by, for the spelling under test.
keyOf :: String -> String
keyOf source = case parseProp source of
  Right p -> ND.encodeAtomKey (nf p)
  Left err -> error ("FormulaNamesSpec: unparsable fixture prop: " ++ show err)

-- ---------------------------------------------------------------------------
-- The rendered block
-- ---------------------------------------------------------------------------

-- | The load-bearing case: a mismatch names two atoms drawn from two different
-- sources, and both are spelled back.
--
-- The @expected@ side is the author's @(prop …)@ annotation; the @got@ side is
-- leaf @e1@'s conclusion, which was never spelled as a @prop@ at all. A map
-- built from annotations alone would explain exactly the first line and leave
-- the reader to decode the second — so this is the property that fixes the
-- design, not merely the output.
prop_bothSidesOfAMismatchAreSpelled :: Property
prop_bothSidesOfAMismatchAreSpelled = once $
  case authorLines s8Mismatch of
    Left err -> counterexample err False
    Right ls ->
      formulaBlock ls
        === [ "  formula 0 = holds(other_invariant, D)  (authored annotation)"
            , "  formula 1 = holds(safety_invariant, D)  (leaf e1)"
            ]

-- | The lines follow the order the __reason__ names the keys, not the order the
-- source declares them.
--
-- Here the leaf is declared before the annotation, and the annotation is still
-- printed first, because the backend reports @expected@ before @got@. Ordering
-- by declaration would put the reader's two lines in the opposite order from
-- the two keys they explain, one line above.
prop_orderFollowsTheReason :: Property
prop_orderFollowsTheReason = once $
  case authorLines s8Mismatch of
    Left err -> counterexample err False
    Right ls ->
      let block = formulaBlock ls
          reason = unlines (takeWhile (\l -> take 10 l /= "  formula ") ls)
          annotationAt = indexOfKey (keyOf "holds(other_invariant, D)") reason
          leafAt = indexOfKey (keyOf "holds(safety_invariant, D)") reason
       in counterexample ("block: " ++ show block) $
            conjoin
              [ counterexample "annotation key precedes leaf key in the reason" $
                  property (annotationAt < leafAt)
              , counterexample "and the block follows that order" $
                  property (map (take 13) block == ["  formula 0 =", "  formula 1 ="])
              , counterexample "annotation line first" $
                  property (any ("other_invariant" `isInfixOf`) (take 1 block))
              ]
  where
    indexOfKey key haystack =
      length (takeWhile (not . (show key `isPrefixOfL`)) (tailsL haystack))
    isPrefixOfL p s = take (length p) s == p
    tailsL s = case s of
      [] -> [[]]
      _ : cs -> s : tailsL cs

-- | An accepting artifact prints no formula block.
--
-- The block is gated on there being a rejection reason to explain, so the
-- @examples\/S8@ artifact as shipped — which accepts — reaches none of this.
prop_acceptIsSilent :: Property
prop_acceptIsSilent = once $
  case authorLines (s8ProgramWith "holds(safety_invariant, D)") of
    Left err -> counterexample err False
    Right ls -> formulaBlock ls === []

-- ---------------------------------------------------------------------------
-- The recovered map
-- ---------------------------------------------------------------------------

-- | The map covers both sources, keyed by the spelling the backend uses.
--
-- It is a property of the __source__, not of the verdict, so both entries are
-- present even though the reason will go on to name only some of them.
prop_mapCoversAnnotationAndLeaf :: Property
prop_mapCoversAnnotationAndLeaf = once $
  case authoredFormulas s8Mismatch of
    Left err -> counterexample err False
    Right fs ->
      conjoin
        [ counterexample "the annotation" $
            lookupKey (keyOf "holds(other_invariant, D)") fs
              === Just ("holds(other_invariant, D)", FOAnnotation)
        , counterexample "the leaf" $
            lookupKey (keyOf "holds(safety_invariant, D)") fs
              === Just ("holds(safety_invariant, D)", FOLeaf (LeafId "e1"))
        ]
  where
    lookupKey k fs = case [f | f <- fs, afKey f == k] of
      f : _ -> Just (afSpelling f, afOrigin f)
      [] -> Nothing

-- | A proposition spelled __both__ ways reports the annotation, once.
--
-- @examples\/S8@ as shipped is exactly this artifact: the annotation and leaf
-- @e1@ carry the same proposition, so they share a key. The author's own words
-- for the position under diagnosis win, and the duplicate is dropped rather
-- than printed twice.
prop_annotationWinsOverLeafOnASharedKey :: Property
prop_annotationWinsOverLeafOnASharedKey = once $
  case authoredFormulas (s8ProgramWith "holds(safety_invariant, D)") of
    Left err -> counterexample err False
    Right fs ->
      [(afSpelling f, afOrigin f) | f <- fs, afKey f == keyOf "holds(safety_invariant, D)"]
        === [("holds(safety_invariant, D)", FOAnnotation)]

-- ---------------------------------------------------------------------------
-- The renderer, in isolation
-- ---------------------------------------------------------------------------

-- | A key the reason does not name contributes no line.
--
-- This is what keeps the block short on a large program: the map grows with the
-- source, the block grows with the rejection.
prop_unmentionedKeysAreSilent :: Property
prop_unmentionedKeysAreSilent = once $
  formulaMappingLines
    ("expected " ++ show (keyOf "holds(safety_invariant, D)"))
    [ AuthoredFormula (keyOf "holds(safety_invariant, D)") "holds(safety_invariant, D)" FOAnnotation
    , AuthoredFormula (keyOf "holds(other_invariant, D)") "holds(other_invariant, D)" FOAnnotation
    ]
    === ["  formula 0 = holds(safety_invariant, D)  (authored annotation)"]

-- | An empty reason, and an empty map, both render nothing.
prop_rendererEmptyCases :: Property
prop_rendererEmptyCases = once $
  conjoin
    [ formulaMappingLines "" [AuthoredFormula "k" "p" FOAnnotation] === []
    , formulaMappingLines "some reason" [] === []
    ]

-- ---------------------------------------------------------------------------
-- The collector, in isolation
-- ---------------------------------------------------------------------------

-- | The payload scan finds every @(prop …)@ node and keys it through the same
-- @encodeAtomKey . nf . parseProp@ path the lowering emits through.
prop_collectorFindsNestedAnnotations :: Property
prop_collectorFindsNestedAnnotations = once $
  authoredPropAnnotations payload
    === [ (keyOf "holds(safety_invariant, D)", "holds(safety_invariant, D)")
        , (keyOf "holds(other_invariant, D)", "holds(other_invariant, D)")
        ]
  where
    payload =
      SList
        [ SAtom "app"
        , SList
            [ SAtom "lam"
            , SAtom "h"
            , SList [SAtom "prop", SAtom "holds(safety_invariant, D)"]
            , SList [SAtom "prem", SAtom "e1"]
            ]
        , SList [SAtom "prop", SAtom "holds(other_invariant, D)"]
        ]

-- | An annotation whose text does not parse contributes nothing.
--
-- Such a payload cannot have lowered, so no key of its exists to explain; the
-- collector reports the absence rather than inventing a key.
prop_collectorSkipsUnparsableAnnotations :: Property
prop_collectorSkipsUnparsableAnnotations = once $
  authoredPropAnnotations (SList [SAtom "prop", SAtom "holds(("]) === []

formulaNamesSpecProps :: [(String, IO Result)]
formulaNamesSpecProps =
  [ ("#148 both sides of a mismatch are spelled", quickCheckResult prop_bothSidesOfAMismatchAreSpelled)
  , ("#148 the block follows the reason's order", quickCheckResult prop_orderFollowsTheReason)
  , ("#148 an accepting artifact prints no formula block", quickCheckResult prop_acceptIsSilent)
  , ("#148 the map covers annotations and leaves", quickCheckResult prop_mapCoversAnnotationAndLeaf)
  , ("#148 a shared key reports the annotation once", quickCheckResult prop_annotationWinsOverLeafOnASharedKey)
  , ("#148 unmentioned keys are silent", quickCheckResult prop_unmentionedKeysAreSilent)
  , ("#148 the renderer's empty cases", quickCheckResult prop_rendererEmptyCases)
  , ("#148 the collector finds nested annotations", quickCheckResult prop_collectorFindsNestedAnnotations)
  , ("#148 the collector skips unparsable annotations", quickCheckResult prop_collectorSkipsUnparsableAnnotations)
  ]
