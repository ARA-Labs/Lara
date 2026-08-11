-- | Σ inference bootstrap (#89 D0) — __tooling, not a language feature__.
--
-- Sort inference is deliberately outside the calculus (#89 §11): LARA terms are
-- ground first-order with no abstraction, application, or polymorphism and no
-- site to put an annotation, so a declared signature already delivers the
-- zero-annotation property inference would have been for. This script exists
-- once, to author the signatures the corpus was written without.
--
-- It is __not a sweep__. A nullary constant has no argument positions, so its
-- sort cannot be read off its own spelling: it must be inferred from the
-- predicate and constructor argument positions it /occupies/, and a constant
-- appearing under two heads forces those positions to share a sort. That is a
-- union-find over occurrences, and the 187 nullary constants of @corpus-v1@ are
-- the dominant term a head-token grep misses entirely (#89 §7).
--
-- == What it computes
--
-- Occurrence classes, unioned:
--
--   * @NPredArg p i@ — the @i@-th argument position of predicate @p@;
--   * @NConArg k i@  — the @i@-th argument position of constructor @k@;
--   * @NConRes k@    — the result position of constructor @k@;
--   * @NParam r X@   — rule @r@'s parameter @X@.
--
-- A pattern variable at a sorted position unions that position with the
-- parameter's class; a constructor application unions the position with the
-- constructor's result class; a numeric or string literal /pins/ the class to a
-- base sort. Two base pins on one class, or two arities for one symbol, are
-- reported as inconsistencies rather than silently merged.
--
-- == What it emits
--
-- The __finest consistent partition__, with generated opaque sort names
-- @S1, S2, …@ in first-occurrence order — plus a census header. The human pass
-- that follows is __merge-and-name, not authoring__ (#89 §7, OV-2): whether
-- @imagenet_val@ is a @Dataset@ or an @EvalSetting@ is precisely the
-- possible-worlds question, and an opaque name presumes no answer. The finest
-- partition also maximizes @wrong-arg-sort@'s corpus sites, keeping R2
-- non-vacuous on real data.
--
-- Inference runs over __elaborated units__, not raw declarations: elaboration
-- is what reclassifies a non-parameter pattern identifier into the nullary
-- constant it actually is, and what expands @comparison@ blocks into the
-- arguments whose θ ties constants to parameter classes.
--
-- >  cabal exec -- runghc --ghc-arg=-package --ghc-arg=lara \
-- >    scripts/infer-sigma.hs <policy.lara> <program.lara>...
--
-- With no program arguments it infers from the policy alone (the rules,
-- contraries, exceptions, and theory table), which is the right mode for a
-- policy whose corpus is not yet written.
module Main (main) where

import Data.List (intercalate, nub, sortOn)
import qualified Data.Map.Strict as M
import System.Environment (getArgs)
import System.Exit (die)

import Lara.AST
import Lara.Elaborate (registryOf)
import Lara.Elaborate.Internal (elaborate)
import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..))
import Lara.Sigma
  ( ConSig (..)
  , PredSig (..)
  , Sigma (..)
  , Sort (..)
  , SortName (..)
  , sortText
  )
import Lara.Syntax (parsePolicy, parseProgram)

-- ---------------------------------------------------------------------------
-- Occurrence classes
-- ---------------------------------------------------------------------------

data Node
  = NPredArg Pred Int
  | NConArg FunSym Int
  | NConRes FunSym
  | NParam RuleId Param
  deriving (Eq, Ord, Show)

renderNode :: Node -> String
renderNode n = case n of
  NPredArg (Pred p) i -> p ++ "/arg" ++ show i
  NConArg (FunSym k) i -> k ++ "/arg" ++ show i
  NConRes (FunSym k) -> k ++ "/result"
  NParam (RuleId r) (Param x) -> r ++ "." ++ x

-- | Inference state: the union-find parent map, base-sort pins per class
-- representative, declared arities, and first-occurrence order for stable
-- naming.
data S = S
  { sParent :: M.Map Node Node
  , sPin :: M.Map Node Sort -- ^ keyed by representative
  , sPredArity :: M.Map Pred Int
  , sConArity :: M.Map FunSym Int
  , sOrder :: [Node] -- ^ reverse first-occurrence order
  , sFaults :: [String] -- ^ reverse order
  }

empty :: S
empty = S M.empty M.empty M.empty M.empty [] []

note :: Node -> S -> S
note n s
  | n `M.member` sParent s = s
  | otherwise = s{sParent = M.insert n n (sParent s), sOrder = n : sOrder s}

findRep :: Node -> S -> (Node, S)
findRep n s0 =
  let s = note n s0
   in case M.lookup n (sParent s) of
        Just p | p /= n -> findRep p s
        _ -> (n, s)

union :: Node -> Node -> S -> S
union a b s0 =
  let (ra, s1) = findRep a s0
      (rb, s2) = findRep b s1
   in if ra == rb
        then s2
        else
          let merged = s2{sParent = M.insert rb ra (sParent s2)}
              pinA = M.lookup ra (sPin s2)
              pinB = M.lookup rb (sPin s2)
              -- The surviving representative keeps a base pin from either side;
              -- two different pins are the reported inconsistency.
              withPin s = case (pinA, pinB) of
                (Nothing, Nothing) -> s
                (Just x, _) -> s{sPin = M.insert ra x (M.delete rb (sPin s))}
                (Nothing, Just y) -> s{sPin = M.insert ra y (M.delete rb (sPin s))}
              conflicted = case (pinA, pinB) of
                (Just x, Just y) | x /= y -> Just (mismatch ra rb x y)
                _ -> Nothing
           in maybe (withPin merged) (\m -> withPin (fault m merged)) conflicted
  where
    mismatch ra rb x y =
      "base-sort conflict: " ++ renderNode ra ++ " is " ++ sortText x
        ++ " but " ++ renderNode rb ++ " is " ++ sortText y

pin :: Node -> Sort -> S -> S
pin n srt s0 =
  let (r, s1) = findRep n s0
   in case M.lookup r (sPin s1) of
        Nothing -> s1{sPin = M.insert r srt (sPin s1)}
        Just old
          | old == srt -> s1
          | otherwise ->
              fault
                ( "base-sort conflict at " ++ renderNode r ++ ": "
                    ++ sortText old ++ " vs " ++ sortText srt
                )
                s1

fault :: String -> S -> S
fault msg s = s{sFaults = msg : sFaults s}

arityPred :: Pred -> Int -> S -> S
arityPred p n s = case M.lookup p (sPredArity s) of
  Just m
    | m /= n ->
        fault ("predicate arity conflict for " ++ (let Pred h = p in h) ++ ": " ++ show m ++ " vs " ++ show n) s
  _ -> s{sPredArity = M.insert p n (sPredArity s)}

arityCon :: FunSym -> Int -> S -> S
arityCon k n s = case M.lookup k (sConArity s) of
  Just m
    | m /= n ->
        fault ("constructor arity conflict for " ++ (let FunSym c = k in c) ++ ": " ++ show m ++ " vs " ++ show n) s
  _ -> s{sConArity = M.insert k n (sConArity s)}

-- ---------------------------------------------------------------------------
-- Traversal
-- ---------------------------------------------------------------------------

visitTerm :: Node -> Term -> S -> S
visitTerm at t s = case t of
  TNum _ -> pin at SortNum s
  TStr _ -> pin at SortStr s
  TCon k ts ->
    let s1 = arityCon k (length ts) (union at (NConRes k) s)
     in foldl (\acc (i, x) -> visitTerm (NConArg k i) x acc) s1 (zip [0 ..] ts)

visitProp :: Prop -> S -> S
visitProp (Prop p ts) s =
  let s1 = arityPred p (length ts) s
      s2 = foldl (\acc i -> note (NPredArg p i) acc) s1 [0 .. length ts - 1]
   in foldl (\acc (i, t) -> visitTerm (NPredArg p i) t acc) s2 (zip [0 ..] ts)

visitPat :: RuleId -> Node -> Pat -> S -> S
visitPat scope at p s = case p of
  PVar x -> union at (NParam scope x) s
  PLit t -> visitTerm at t s
  PCon k ps ->
    let s1 = arityCon k (length ps) (union at (NConRes k) s)
     in foldl (\acc (i, q) -> visitPat scope (NConArg k i) q acc) s1 (zip [0 ..] ps)

visitAPat :: RuleId -> AtomPat -> S -> S
visitAPat scope (AtomPat p ps) s =
  let s1 = arityPred p (length ps) s
      s2 = foldl (\acc i -> note (NPredArg p i) acc) s1 [0 .. length ps - 1]
   in foldl (\acc (i, q) -> visitPat scope (NPredArg p i) q acc) s2 (zip [0 ..] ps)

visitUnit :: Unit -> S -> S
visitUnit u s0 = foldl (flip ($)) s0 (rules ++ excs ++ contras ++ theories ++ leaves ++ queries ++ substs)
  where
    rules =
      [ visitAPat (ruleId r) a
      | r <- unitRules u
      , a <- rulePremises r ++ [ruleConclusion r] ++ map questionAnswer (ruleQuestions r)
      ]
    excs = [visitAPat (exceptionRule e) (exceptionAtom e) | e <- unitExceptions u]
    -- Contraries carry no rule scope; their variables are universally
    -- quantified, but the two sides of one pair share them.
    contras =
      [ visitAPat (RuleId ("#contrary" ++ show i)) a
      | (i, Contrary l r) <- zip [(0 :: Int) ..] (unitContraries u)
      , a <- [l, r]
      ]
    theories = [visitProp p | (_, ps) <- unitTheories u, p <- ps]
    leaves = [visitProp p | (_, p) <- unitLeaves u]
    queries = map visitProp (unitQueries u)
    substs = concatMap (walk . snd) (unitArgs u)
    walk (SLeaf _) = []
    walk (SRule rid theta prems dis _ _) =
      [visitTerm (NParam rid x) t | (x, t) <- theta]
        ++ concatMap walk prems
        ++ concatMap (walk . snd) dis

-- ---------------------------------------------------------------------------
-- Reading the partition out
-- ---------------------------------------------------------------------------

-- | Assign a 'Sort' to every class: a pinned class keeps its base sort, an
-- unpinned one gets the next generated opaque name in first-occurrence order.
solve :: S -> (S, M.Map Node Sort)
solve s0 = go s0 M.empty (0 :: Int) (reverse (sOrder s0))
  where
    go s acc _ [] = (s, acc)
    go s acc n (node : rest) =
      let (r, s') = findRep node s
       in case M.lookup r acc of
            Just _ -> go s' acc n rest
            Nothing -> case M.lookup r (sPin s') of
              Just b -> go s' (M.insert r b acc) n rest
              Nothing ->
                let n' = n + 1
                 in go s' (M.insert r (SortDecl (SortName ("S" ++ show n'))) acc) n' rest

sortAt :: S -> M.Map Node Sort -> Node -> (S, Sort)
sortAt s assign node =
  let (r, s') = findRep node s
   in (s', M.findWithDefault (SortDecl (SortName "S?")) r assign)

buildSigma :: S -> M.Map Node Sort -> (S, Sigma)
buildSigma s0 assign = (sFinal, Sigma decls cons preds)
  where
    (s1, cons) =
      foldl
        ( \(s, acc) (k, n) ->
            let (s', args) = mapAccum s [NConArg k i | i <- [0 .. n - 1]]
                (s'', res) = sortAt s' assign (NConRes k)
             in (s'', acc ++ [ConSig k args res])
        )
        (s0, [])
        (M.toAscList (sConArity s0))
    (sFinal, preds) =
      foldl
        ( \(s, acc) (p, n) ->
            let (s', args) = mapAccum s [NPredArg p i | i <- [0 .. n - 1]]
             in (s', acc ++ [PredSig p args])
        )
        (s1, [])
        (M.toAscList (sPredArity s0))
    mapAccum s [] = (s, [])
    mapAccum s (n : ns) =
      let (s', x) = sortAt s assign n
          (s'', xs) = mapAccum s' ns
       in (s'', x : xs)
    -- Declared sorts in generated-name order, so the printed `sort` line reads
    -- S1, S2, ….
    decls =
      sortOn (\(SortName n) -> (length n, n)) . nub $
        [n | SortDecl n <- M.elems assign]

-- ---------------------------------------------------------------------------
-- Rendering
-- ---------------------------------------------------------------------------

renderSigma :: Sigma -> String
renderSigma sg =
  unlines $
    ["sort " ++ intercalate ", " [n | SortName n <- sigmaSorts sg] | not (null (sigmaSorts sg))]
      ++ [""]
      ++ [ "con " ++ k ++ argVector (conArgs c) ++ " : " ++ sortText (conResult c)
         | c <- sigmaCons sg
         , let FunSym k = conSym c
         ]
      ++ [""]
      ++ [ "pred " ++ h ++ argVector (predArgs p)
         | p <- sigmaPreds sg
         , let Pred h = predSym p
         ]
  where
    argVector [] = ""
    argVector ss = "(" ++ intercalate ", " (map sortText ss) ++ ")"

census :: Sigma -> String
census sg =
  unlines
    [ "# census: " ++ show (length (sigmaSorts sg)) ++ " inferred sorts, "
        ++ show (length (sigmaCons sg)) ++ " constructors ("
        ++ show (length [c | c <- sigmaCons sg, null (conArgs c)])
        ++ " nullary), "
        ++ show (length (sigmaPreds sg)) ++ " predicates"
    ]

-- ---------------------------------------------------------------------------
-- Driver
-- ---------------------------------------------------------------------------

main :: IO ()
main = do
  args <- getArgs
  (policyPath, programPaths) <- case args of
    (p : ps) -> pure (p, ps)
    _ -> die "usage: infer-sigma.hs <policy.lara> [program.lara ...]"
  policyText <- readFile policyPath
  policy <- either (die . ((policyPath ++ ": parse: ") ++) . show) pure (parsePolicy policyText)
  units <- mapM (loadUnit policy) programPaths
  -- With no programs, the policy alone still fixes every rule-side occurrence.
  let seedUnit = policyOnlyUnit policy
      s1 = foldl (flip visitUnit) empty (seedUnit : units)
      (s2, assign) = solve s1
      (s3, sigma) = buildSigma s2 assign
  case reverse (sFaults s3) of
    [] -> pure ()
    fs -> die ("inconsistent corpus:\n  " ++ intercalate "\n  " fs)
  putStr (census sigma)
  putStr (renderSigma sigma)

-- | Elaborate one program against the policy so inference sees reclassified
-- patterns and expanded @comparison@ blocks.
loadUnit :: Policy -> FilePath -> IO Unit
loadUnit policy path = do
  text <- readFile path
  prog <- either (die . ((path ++ ": parse: ") ++) . show) pure (parseProgram text)
  either (die . ((path ++ ": elaborate: ") ++) . show) pure
    (elaborate (registryOf policy) prog policy)

-- | The policy's own occurrences, as a unit with no program material. Built
-- directly rather than by elaborating an empty program, because an empty
-- program has no @status@ declaration and would fail the source boundary.
policyOnlyUnit :: Policy -> Unit
policyOnlyUnit pol =
  Unit
    { unitSigma = Sigma [] [] []
    , unitRules = policyRules reclassified
    , unitContraries = policyContraries reclassified
    , unitExceptions = policyExceptions reclassified
    , unitTheories = policyTheories reclassified
    , unitLeaves = []
    , unitArgs = []
    , unitAttacks = []
    , unitQueries = []
    , unitGroups = []
    , unitGroupMode = policyGroupMode reclassified
    }
  where
    -- The elaborator's own reclassification, applied here so a policy inferred
    -- without programs sees the same nullary constants a program run would.
    reclassified =
      pol
        { policyRules = map reclassifyRule (policyRules pol)
        , policyExceptions = map (reclassifyException (policyRules pol)) (policyExceptions pol)
        }
    reclassifyRule r =
      r
        { rulePremises = map (reclassifyAPat (ruleParams r)) (rulePremises r)
        , ruleConclusion = reclassifyAPat (ruleParams r) (ruleConclusion r)
        , ruleQuestions =
            [q{questionAnswer = reclassifyAPat (ruleParams r) (questionAnswer q)} | q <- ruleQuestions r]
        }
    reclassifyException rules ex = case [r | r <- rules, ruleId r == exceptionRule ex] of
      r : _ -> ex{exceptionAtom = reclassifyAPat (ruleParams r) (exceptionAtom ex)}
      [] -> ex
    reclassifyAPat params (AtomPat pr ps) = AtomPat pr (map (reclassifyPat params) ps)
    reclassifyPat params q = case q of
      PVar prm@(Param x)
        | prm `elem` params -> q
        | otherwise -> PCon (FunSym x) []
      PCon k ps -> PCon k (map (reclassifyPat params) ps)
      PLit _ -> q
