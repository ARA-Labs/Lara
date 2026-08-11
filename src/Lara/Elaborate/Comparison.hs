-- | The @lara-syntax\@0.3@ surface expansion: a presentation-to-presentation
-- pass that replaces every @comparison@ block (grammar App. B.3) with the
-- ordinary @claim@ and @arg@ declarations it stands for, and interpolates the
-- @nl@ directives of B.6 on the way.
--
-- == Why presentation → presentation
--
-- The expansion emits 'Decl's and splices them into the declaration list in
-- place, rather than building 'SupportTerm's for the 'Unit' directly. That is
-- the point of the design, not an implementation convenience:
--
--   * the generated arguments then go through the /same/ lowering a
--     hand-authored @arg@ does — @resolvePremises@' unique @≡@-match,
--     @resolveDischarges@, and the @supports(c)@ conclusion check — so
--     "byte-identical to the hand-written source" is true by construction and
--     not by two code paths agreeing;
--   * the announced conclusion of each generated argument is checked by the
--     existing 'Lara.Elaborate.Error.ConclusionMismatch' path, which is exactly
--     App. B.3's "authored conclusion vs. the supported claim's @formal@"
--     error — no second implementation of it exists;
--   * a later deliverable that needs the expansion as data (D5's surface
--     diagnostics) gets it from 'expandSurface' without re-deriving anything.
--
-- The shape emitted therefore matches what "Lara.Syntax" produces for an
-- equivalent hand-written source: a rule support term carries θ /positionally/
-- and leaves @srPremises@ empty for the elaborator to reconstruct.
--
-- == Expansion order (plan §5)
--
-- 1. the measurand's declared polarity (App. B.1);
-- 2. the @comparison-scheme@ for the pair (relation, polarity) (App. B.2);
-- 3. θ by __one-way matching__ ("Lara.Elaborate.Subst") of the named
--    @result@\/@baseline@ leaves against the recheck rule's premise patterns
--    and of the authored conclusion against the bridge's conclusion pattern,
--    binding /every/ parameter of both rules — including ones like @Exp@ that
--    appear in no comparison field — with a twice-bound parameter required to
--    agree;
-- 4. the sub-claim: authored @nl@ and @binding@, __generated @formal@__;
-- 5. the recheck argument, with @assurance = cert(ord\@1, …, (ordcmp (prem i)
--    (prem j)))@ over __0-based__ slots — and, before the certificate is
--    formed, the __direction-of-goodness check__: the goal's operand order,
--    attributed to @result@\/@baseline@ by provenance, must be the order the
--    declared polarity means, or the scheme is rejected;
-- 6. the bridge argument over the generated comparison and the named binding
--    leaf.
--
-- Step 5's direction check is what keeps @polarity@ load-bearing past scheme
-- /selection/. Without it a policy whose recheck and bridge rules are flipped
-- /together/ stays internally consistent — the shared variables still weld the
-- two rules to each other — while certifying the opposite of what the polarity
-- declares. It is the Haskell counterpart of @Lara.Comparison.goalOf@ (lean\/),
-- which computes the same table from the polarity.
--
-- Every failure is a dedicated 'ElabError'. 'Lara.Strict.Cell.premiseCell' is
-- reused for /extraction/ only; its backend-worded @Left String@ never reaches
-- an author (plan §6.1.1, 7A).
module Lara.Elaborate.Comparison
  ( expandSurface
  , expandSurfaceProvenance
  , expandClaimNls
  , GeneratedArg (..)
  , expandNl
  ) where

import Control.Monad (foldM, when)
import Data.List (find, nub)

import Lara.AST
import Lara.Elaborate.Error (ElabError (..))
import Lara.Elaborate.Subst (apatToProp, matchAPat, patToTerm, sameTerm)
import Lara.Prop (Prop (..), Term (..))
import Lara.Syntax (nlCellDirective)
import Lara.Strict (SExpr (..))
import qualified Lara.Strict as Strict
import qualified Lara.Strict.Cell as Cell
import qualified Lara.Strict.Ord as OrdB

-- ---------------------------------------------------------------------------
-- The provenance breadcrumb (plan D5)
-- ---------------------------------------------------------------------------

-- | One generated argument, tied back to the authored @comparison@ block that
-- minted it and to the three surface fields an author can act on.
--
-- __Diagnostic metadata, never program content.__ This exists so that a
-- rejection reported against a /generated/ argument can be framed in the
-- author's own vocabulary before the kernel's wording is shown. It is
-- deliberately __not__ reachable from 'Unit': 'expandSurfaceProvenance' returns
-- it beside the expanded 'Program' rather than inside it, and
-- 'Lara.Elaborate.Internal.elaborate' — the only function that builds a 'Unit'
-- — discards it. The @examples\/*\/example.core.sexp@ goldens are the standing
-- proof: a breadcrumb that reached the checker anchor would move their bytes.
data GeneratedArg = GeneratedArg
  { gaArgId :: ArgId
  -- ^ the generated argument's id (author-declared: @recheck@ or @bridge@)
  , gaClaimId :: PropId
  -- ^ the block's @claims@ id, which is how every other surface diagnostic
  -- names a @comparison@ (see 'Lara.Elaborate.Error.elabErrorMessage')
  , gaResult :: LeafId -- ^ the @result@ field
  , gaBaseline :: LeafId -- ^ the @baseline@ field
  , gaMeasurand :: MeasurandId -- ^ the @on \<measurand\>@ field
  }
  deriving (Eq, Show)

-- ---------------------------------------------------------------------------
-- The pass
-- ---------------------------------------------------------------------------

-- | Resolve every ordinary claim's @nl@ body against the program's complete
-- declared-leaf table. The result is semantic prose, not the raw brace spelling
-- consumed by 'Lara.Syntax.printProgram'; callers must not send the
-- post-expansion value back through the surface printer.
expandClaimNls :: Program -> Either ElabError Program
expandClaimNls prog = do
  decls <- mapM one (programDecls prog)
  pure prog {programDecls = decls}
  where
    gamma = [(leafId l, leafProp l) | DeclLeaf l <- programDecls prog]
    one d = case d of
      DeclClaim c -> DeclClaim <$> expandClaimNl gamma c
      _ -> Right d

expandClaimNl :: [(LeafId, Prop)] -> Claim -> Either ElabError Claim
expandClaimNl gamma c = do
  nl <- expandNl (claimId c) gamma (claimNl c)
  pure c {claimNl = nl}

-- | Expand every @comparison@ block of a program in place (grammar App. B.3).
--
-- The result is the semantic presentation consumed by structural lowering: it
-- carries no 'DeclComparison', and all claim @nl@ bodies have been interpolated.
-- Declaration order is preserved, fixing AF node indices. This is deliberately
-- a one-way phase boundary, not another input to the raw surface
-- parse\/print round trip.
expandSurface :: Policy -> Program -> Either ElabError Program
expandSurface pol prog = fst <$> expandSurfaceProvenance pol prog

-- | 'expandSurface' paired with the 'GeneratedArg' breadcrumb for every
-- argument the expansion minted, in declaration order.
--
-- The two halves come from one pass, so a breadcrumb can never describe an
-- argument this expansion did not emit. Callers that only need the program keep
-- using 'expandSurface'.
expandSurfaceProvenance :: Policy -> Program -> Either ElabError (Program, [GeneratedArg])
expandSurfaceProvenance pol prog = do
  checkGeneratedIds decls blocks
  checkDuplicateBlocks blocks
  expanded <- mapM one decls
  pure (prog {programDecls = concatMap fst expanded}, concatMap snd expanded)
  where
    decls = programDecls prog
    blocks = [c | DeclComparison c <- decls]
    -- Γ for the expansion: leaves are never generated (App. B.3 — the
    -- attestation leaf stays a human claim), so the declared table is complete
    -- before any block expands.
    gamma = [(leafId l, leafProp l) | DeclLeaf l <- decls]
    one d = case d of
      DeclClaim c -> do
        expandedClaim <- expandClaimNl gamma c
        Right ([DeclClaim expandedClaim], [])
      DeclComparison c -> expandComparison pol gamma c
      _ -> Right ([d], [])

-- | The generated @recheck@\/@bridge@\/@claims@ ids must collide with nothing:
-- not with a declared declaration, and not with another block's (App. B.3).
-- Checked before any block expands, so the report names the colliding id rather
-- than the duplicate-id error a later stage would raise.
checkGeneratedIds :: [Decl] -> [Comparison] -> Either ElabError ()
checkGeneratedIds decls = go [] []
  where
    declaredArgs = [a | DeclArg x <- decls, let ArgId a = argId x]
    declaredClaims = [c | DeclClaim x <- decls, let PropId c = claimId x]
    go _ _ [] = Right ()
    go seenArgs seenClaims (c : rest) = do
      let cid = ccId (cmpClaim c)
          ArgId recheckId = cmpRecheckArg c
          ArgId bridgeId = cmpBridgeArg c
          PropId claimName = cid
      when (recheckId == bridgeId) $ Left (ComparisonIdCollision cid bridgeId)
      when (recheckId `elem` declaredArgs ++ seenArgs) $
        Left (ComparisonIdCollision cid recheckId)
      when (bridgeId `elem` declaredArgs ++ seenArgs) $
        Left (ComparisonIdCollision cid bridgeId)
      when (claimName `elem` declaredClaims ++ seenClaims) $
        Left (ComparisonIdCollision cid claimName)
      go (seenArgs ++ [recheckId, bridgeId]) (seenClaims ++ [claimName]) rest

-- | Two blocks stating the same comparison — the same pair of cells, on the
-- same measurand and dataset, under the same relation — are a source error
-- (App. B.3, "duplicate or overlapping @comparison@ blocks"): they would emit
-- two arguments for one fact, which the checker's duplicate-argument rule would
-- then reject far from the declaration that caused it.
checkDuplicateBlocks :: [Comparison] -> Either ElabError ()
checkDuplicateBlocks = go []
  where
    key c = (cmpResult c, cmpBaseline c, cmpMeasurand c, cmpDataset c, cmpRelation c)
    go _ [] = Right ()
    go seen (c : rest) = case lookup (key c) seen of
      Just earlier -> Left (ComparisonDuplicateBlock (ccId (cmpClaim c)) earlier)
      Nothing -> go (seen ++ [(key c, ccId (cmpClaim c))]) rest

-- ---------------------------------------------------------------------------
-- One block
-- ---------------------------------------------------------------------------

-- | Expand one @comparison@ into the three declarations it stands for, in the
-- order plan §5 states: the sub-claim, the strict recheck argument, the
-- defeasible bridge argument — plus the 'GeneratedArg' breadcrumb for the two
-- arguments, which travels beside the declarations and never inside them.
expandComparison
  :: Policy
  -> [(LeafId, Prop)]
  -> Comparison
  -> Either ElabError ([Decl], [GeneratedArg])
expandComparison pol gamma cmp = do
  -- (1) polarity — declared domain knowledge, never inferred (App. B.1).
  polarity <- case find ((== cmpMeasurand cmp) . measurandId) (policyMeasurands pol) of
    Just m -> case measurandPolarity m of
      Just p -> Right p
      Nothing -> Left (ComparisonMeasurandNoPolarity cid (cmpMeasurand cmp))
    Nothing -> Left (ComparisonUndeclaredMeasurand cid (cmpMeasurand cmp))
  -- (2) the scheme for the *pair*; relation alone cannot express direction.
  let matchesPair s = csRelation s == cmpRelation cmp && csPolarity s == polarity
  scheme <- case find matchesPair (policyComparisonSchemes pol) of
    Just s -> Right s
    Nothing -> Left (ComparisonNoScheme cid (cmpRelation cmp) polarity)
  recheck <- schemeRule (csRecheck scheme)
  bridge <- schemeRule (csBridge scheme)
  -- Scheme well-formedness (App. B.2), in the order the grammar lists it.
  when (ruleMode recheck /= Strict) $
    Left (ComparisonRecheckNotStrict cid (ruleId recheck))
  certRef <- ordCertifier recheck
  (goalLeft, goalRight) <- case ruleConclusion recheck of
    AtomPat _ [l, r] -> Right (l, r)
    _ -> Left (ComparisonRecheckConclusionShape cid (ruleId recheck))
  when (ruleMode bridge /= Defeasible) $
    Left (ComparisonBridgeNotDefeasible cid (ruleId bridge))
  (bridgePred, bridgeS, bridgeB, bridgeQ, bridgeD) <- bridgeShape bridge
  -- The authored 2-ary system pair, widened to the 4-ary atom the bridge
  -- declares by the `on`/`@` fields. The scheme check is against the *formed*
  -- atom, never the 2-ary spelling (App. B.2).
  (authoredPred, sysTerm, baseTerm) <- case cmpConclusion cmp of
    Prop p [s, b] -> Right (p, s, b)
    other -> Left (ComparisonConclusionShape cid other)
  when (authoredPred /= bridgePred) $
    Left (ComparisonConclusionPredMismatch cid (ruleId bridge) authoredPred bridgePred)
  let MeasurandId measurandName = cmpMeasurand cmp
      DatasetId datasetName = cmpDataset cmp
      qTerm = TCon (FunSym measurandName) []
      dTerm = TCon (FunSym datasetName) []
      thetaBridgeSeed =
        [ (bridgeS, sysTerm)
        , (bridgeB, baseTerm)
        , (bridgeQ, qTerm)
        , (bridgeD, dTerm)
        ]
  -- The three named leaves. The binding leaf is attested evidence the bridge
  -- consumes and must remain the exact leaf the block names.
  when (cmpResult cmp == cmpBaseline cmp) $ Left (ComparisonSameLeaf cid (cmpResult cmp))
  resultProp <- declaredLeaf (cmpResult cmp)
  baseProp <- declaredLeaf (cmpBaseline cmp)
  bindingProp <- case lookup (cmpBinding cmp) gamma of
    Just p -> Right p
    Nothing -> Left (ComparisonBindingNotLeaf cid (cmpBinding cmp))
  ( bridgeBindingSlot
    , bridgeResultValue
    , bridgeBaseValue
    , bridgeComparisonSlot
    , bridgeComparisonPat
    , bridgeBindingPat
    ) <-
      bridgePremiseShape bridge bridgeS bridgeB bridgeQ bridgeD
  recheckResultValue <-
    recoverRecheckRole
      recheck
      bridgeS
      (correspondingRecheckParam recheck bridgeResultValue (ruleConclusion recheck) bridgeComparisonPat)
  recheckBaseValue <-
    recoverRecheckRole
      recheck
      bridgeB
      (correspondingRecheckParam recheck bridgeBaseValue (ruleConclusion recheck) bridgeComparisonPat)
  -- (3a) the premise-cell obligation, as a *source* precondition of the form.
  resultCell <- leafCell (cmpResult cmp) resultProp
  baseCell <- leafCell (cmpBaseline cmp) baseProp
  -- (3b) which premise slot each named leaf occupies. The bridge's binding
  -- premise associates its result/baseline value parameters with the authored
  -- systems. Structural correspondence through the bridge comparison premise
  -- transfers those roles to the independently named recheck parameters.
  let slots = zip [0 ..] (rulePremises recheck)
  (resultSlot, subResult) <-
    uniqueSlot recheck (cmpResult cmp) slots recheckResultValue resultProp
  (baseSlot, subBase) <-
    uniqueSlot recheck (cmpBaseline cmp) slots recheckBaseValue baseProp
  when (resultSlot == baseSlot) $ Left (ComparisonSlotClash cid (ruleId recheck) resultSlot)
  -- (3c) Normalize the authored S/B/Q/D terms into the recheck rule's own key
  -- space before merging the two premise matches. A recheck rule may rename
  -- every parameter independently of the bridge; conflicts must still meet on
  -- the recheck keys that the matched leaves expose.
  let roleParams term =
        nub
          [ p
          | sub <- [subResult, subBase]
          , (p, t) <- sub
          , sameTerm t term
          ]
  recheckS <- requireRole recheck "result system" (roleParams sysTerm)
  recheckB <- requireRole recheck "baseline system" (roleParams baseTerm)
  recheckQ <- requireRole recheck "measurand" (roleParams qTerm)
  recheckD <- requireRole recheck "dataset" (roleParams dTerm)
  let thetaRecheckSeed =
        [(p, sysTerm) | p <- recheckS]
          ++ [(p, baseTerm) | p <- recheckB]
          ++ [(p, qTerm) | p <- recheckQ]
          ++ [(p, dTerm) | p <- recheckD]
      bindOne lid acc (v, t) = case lookup v acc of
        Nothing -> Right (acc ++ [(v, t)])
        Just t'
          | sameTerm t' t -> Right acc
          | v `elem` recheckQ ->
              Left (ComparisonMeasurandInconsistent cid lid (cmpMeasurand cmp) t)
          | otherwise ->
              Left (ComparisonThetaConflict cid (cmpBaseline cmp) (cmpResult cmp) v t' t)
      inSlotOrder
        | baseSlot < resultSlot =
            [(cmpBaseline cmp, subBase), (cmpResult cmp, subResult)]
        | otherwise =
            [(cmpResult cmp, subResult), (cmpBaseline cmp, subBase)]
  thetaRecheck <-
    foldM (\acc (lid, sub) -> foldM (bindOne lid) acc sub) thetaRecheckSeed inSlotOrder
  mapM_ (requireBound thetaRecheck recheck) (ruleParams recheck)
  -- (4) the goal atom: the recheck rule's conclusion under its θ. This is the
  -- sub-claim's generated `formal` and the certificate's goal.
  let goal = apatToProp thetaRecheck (ruleConclusion recheck)
  -- (5) the certificate's two 0-based slots, attributed to the named leaves by
  -- *which match introduced the goal's variable* — value-equal cells (S3's tie)
  -- would make a numeric attribution ambiguous, so provenance decides first.
  let domBase = map fst subBase
      domResult = map fst subResult
      undeterminable = ComparisonCertSlotUndeterminable cid (ruleId recheck)
      slotFor pat = case pat of
        PVar v
          | v `elem` domBase, v `notElem` domResult -> Right baseSlot
          | v `elem` domResult, v `notElem` domBase -> Right resultSlot
        _ -> case patToTerm thetaRecheck pat of
          TNum n
            | Just q <- Cell.parseDecimal n ->
                if q == baseCell
                  then Right baseSlot
                  else
                    if q == resultCell
                      then Right resultSlot
                      else Left undeterminable
          _ -> Left undeterminable
  slotL <- slotFor goalLeft
  slotR <- slotFor goalRight
  -- (5a) direction of goodness: the goal's operand order, attributed to the
  -- named leaves by (5)'s provenance, must be the order the declared polarity
  -- means. Without this the polarity is inert after scheme selection: a policy
  -- whose recheck *and* bridge rules are flipped together is internally
  -- consistent — structural correspondence still relates their independently
  -- named parameters — and yet externally backwards, so a worse system
  -- certifies as `better`.
  -- That is verbatim the §1.2 hazard the form exists to remove.
  --
  -- This is the Haskell side of @Lara.Comparison.goalOf@ (lean/), which
  -- *computes* the same table from @pol@; enforcing it here is what makes the
  -- Lean definition a specification of this elaborator rather than a parallel
  -- model of it. App. B.2 states the obligation as scheme well-formedness
  -- checked when a comparison selects that scheme, so the rejection is located
  -- at the comparison use site, not at a backend far downstream.
  let expectedSlots = case csPolarity scheme of
        HigherIsBetter -> (baseSlot, resultSlot) -- rel(base, ours)
        LowerIsBetter -> (resultSlot, baseSlot) -- rel(ours, base)
  when ((slotL, slotR) /= expectedSlots) $
    Left (ComparisonSchemeDirectionMismatch cid (ruleId recheck) (csPolarity scheme))
  -- Match the bridge's two known premises in its own parameter namespace.
  -- Binding first introduces bridge-only value parameters; comparison second
  -- checks that those same values are exactly the recheck result.
  thetaBinding <-
    case matchAPat thetaBridgeSeed bridgeBindingPat bindingProp of
      Right sub -> Right sub
      Left _ -> Left (ComparisonBindingNotAdmitted cid (cmpBinding cmp) (ruleId bridge))
  thetaBridge <-
    case matchAPat thetaBinding bridgeComparisonPat goal of
      Right sub -> Right sub
      Left _ -> Left (ComparisonBridgePremiseShape cid (ruleId bridge))
  mapM_ (requireBound thetaBridge bridge) (ruleParams bridge)
  let payload =
        SList
          [ SAtom (OrdB.tagToString OrdB.TOrdcmp)
          , premRef slotL
          , premRef slotR
          ]
      cert =
        Cert
          (certRefBackend certRef)
          (certRefVersion certRef)
          (certRefTheory certRef)
          payload
  -- (6) the three declarations. Each θ is emitted positionally under its own
  -- rule's parameter order; no parameter identity crosses the rule boundary.
  nl <- expandNl cid gamma (ccNlRaw (cmpClaim cmp))
  let thetaFor theta r = [(p, t) | p <- ruleParams r, Just t <- [lookup p theta]]
      subClaim =
        Claim
          { claimId = cid
          , claimNl = nl
          , claimFormal = goal
          , claimBinding = ccBinding (cmpClaim cmp)
          }
      recheckArg =
        Arg
          { argId = cmpRecheckArg cmp
          , argConcl = SupportsClaim cid
          , argTerm = SRule (ruleId recheck) (thetaFor thetaRecheck recheck) [] [] [] (AssuranceCert cert)
          }
      ArgId bridgeName = cmpBridgeArg cmp
      bridgeArg =
        Arg
          { argId = cmpBridgeArg cmp
          , -- A block with no @supports@ tail announces a derived conclusion.
            -- 'SupportsDerived' is the arm for "this id is not a declared
            -- claim", and the argument's own id is the only name in scope; the
            -- value never reaches 'Unit' (it records the author's stated role),
            -- so the choice is diagnostic-only.
            argConcl = maybe (SupportsDerived (PropId bridgeName)) SupportsClaim (cmpSupports cmp)
          , argTerm =
              SRule
                (ruleId bridge)
                (thetaFor thetaBridge bridge)
                [ if i == bridgeComparisonSlot
                    then argTerm recheckArg
                    else
                      if i == bridgeBindingSlot
                        then SLeaf (cmpBinding cmp)
                        else error "unreachable bridge premise slot"
                | i <- [0 .. length (rulePremises bridge) - 1]
                ]
                []
                []
                AssuranceNone
          }
      crumb aid =
        GeneratedArg
          { gaArgId = aid
          , gaClaimId = cid
          , gaResult = cmpResult cmp
          , gaBaseline = cmpBaseline cmp
          , gaMeasurand = cmpMeasurand cmp
          }
  pure
    ( [DeclClaim subClaim, DeclArg recheckArg, DeclArg bridgeArg]
    , [crumb (cmpRecheckArg cmp), crumb (cmpBridgeArg cmp)]
    )
  where
    cid = ccId (cmpClaim cmp)

    schemeRule rid = case find ((== rid) . ruleId) (policyRules pol) of
      Just r -> Right r
      Nothing -> Left (ComparisonSchemeRuleUnknown cid rid)

    ordCertifier rule =
      case [ c
           | c <- ruleCertifiers rule
           , certRefBackend c == BackendId (Strict.backendName OrdB.ordBackendId)
           , certRefVersion c == Strict.backendVersion OrdB.ordBackendId
           ] of
        (c : _) -> Right c
        [] -> Left (ComparisonRecheckCertifierMissing cid (ruleId rule))

    -- App. B.2 / eng review F4: 4-ary over S, B, Q, D with the favored system
    -- first. Richer bridge conclusions are an explicit non-goal for @0.3.
    bridgeShape rule = case ruleConclusion rule of
      AtomPat p [PVar a, PVar b, PVar q, PVar d]
        | length (nub [a, b, q, d]) == 4 -> Right (p, a, b, q, d)
      _ -> Left (ComparisonBridgeConclusionShape cid (ruleId rule))

    declaredLeaf lid = case lookup lid gamma of
      Just p -> Right p
      Nothing -> Left (ComparisonLeafUndeclared cid lid)

    -- Extraction only: the backend's wording never reaches the author (7A).
    leafCell lid p = case Cell.premiseCell p of
      Right r -> Right r
      Left _ -> Left (ComparisonCellObligation cid lid)

    premRef i = SList [SAtom (Cell.tagToString Cell.TPrem), SAtom (show i)]

    requireBound theta rule prm =
      case lookup prm theta of
        Just _ -> Right ()
        Nothing -> Left (ComparisonUnboundParam cid (ruleId rule) prm)

    requireRole rule role ps
      | null ps = Left (ComparisonRecheckRoleMissing cid (ruleId rule) role)
      | otherwise = Right ps

    bridgePremiseShape rule bridgeS bridgeB bridgeQ bridgeD =
      case zip [0 ..] (rulePremises rule) of
        [(i, p), (j, q)] ->
          case (bindingValues p, bindingValues q) of
            (Just values, Nothing) -> pack i values j q p
            (Nothing, Just values) -> pack j values i p q
            _ -> Left badShape
        _ -> Left badShape
      where
        badShape = ComparisonBridgePremiseShape cid (ruleId rule)
        bindingValues pat = case pat of
          AtomPat _ [PVar s, PVar b, PVar q, PVar d, PVar sv, PVar bv]
            | (s, b, q, d) == (bridgeS, bridgeB, bridgeQ, bridgeD)
            , length (nub [s, b, q, d, sv, bv]) == 6 ->
                Just (sv, bv)
          _ -> Nothing
        pack bindingSlot (sv, bv) comparisonSlot comparisonPat bindingPat =
          Right (bindingSlot, sv, bv, comparisonSlot, comparisonPat, bindingPat)

    correspondingRecheckParam rule bridgeParam recheckPat bridgePat =
      case alignedParams recheckPat bridgePat of
        Just pairs
          | [p] <- nub [r | (r, b) <- pairs, b == bridgeParam] -> Right p
        _ -> Left (ComparisonBridgePremiseShape cid (ruleId rule))

    -- A literal goal operand has no parameter correspondence. Preserve the
    -- existing certificate-slot diagnostic in that malformed case by falling
    -- back to a same-named system parameter when the policy uses one. Normal
    -- comparison schemes, including independently renamed recheck rules, take
    -- the structural correspondence path above.
    recoverRecheckRole rule fallback attempt =
      case attempt of
        Right p -> Right p
        Left e
          | fallback `elem` ruleParams rule -> Right fallback
          | otherwise -> Left e

    alignedParams (AtomPat p ps) (AtomPat q qs)
      | p == q, length ps == length qs =
          fmap concat (sequence (zipWith alignedPat ps qs))
      | otherwise = Nothing

    alignedPat (PVar a) (PVar b) = Just [(a, b)]
    alignedPat (PCon f ps) (PCon g qs)
      | f == g, length ps == length qs =
          fmap concat (sequence (zipWith alignedPat ps qs))
    alignedPat (PLit a) (PLit b)
      | sameTerm a b = Just []
    alignedPat _ _ = Nothing

    uniqueSlot rule lid slots valueParam prop =
      case [ (i, sub)
           | (i, pat) <- slots
           , Right sub <- [matchAPat [] pat prop]
           , valueParam `elem` map fst sub
           ] of
        [x] -> Right x
        [] -> Left (ComparisonNoPremiseSlot cid (ruleId rule) lid)
        xs -> Left (ComparisonAmbiguousPremiseSlot cid (ruleId rule) lid (map fst xs))

-- ---------------------------------------------------------------------------
-- nl interpolation (grammar App. B.6)
-- ---------------------------------------------------------------------------

-- | Expand a raw @nl@ body: @{{@\/@}}@ become literal braces and @{cell l}@
-- becomes the numeric cell of leaf @l@, rendered through
-- 'Lara.Strict.Cell.renderDecimal'.
--
-- Applied to every claim-form @nl@: both §3's ordinary @claim@ declaration
-- and the @claims … nl@ nested in an App. B.3 @comparison@ block. The parser
-- gives both forms the same strict brace contract, and this pass resolves
-- directives only after the complete declared-leaf table is available.
--
-- Strict, not lenient (App. B.6): a mistyped @{cel e2}@ is an error rather than
-- frozen prose, which is the prose↔formal staleness this feature exists to
-- kill.
expandNl :: PropId -> [(LeafId, Prop)] -> String -> Either ElabError String
expandNl cid gamma = go
  where
    go s = case s of
      [] -> Right ""
      '{' : '{' : rest -> ('{' :) <$> go rest
      '}' : '}' : rest -> ('}' :) <$> go rest
      '}' : _ -> Left (NlStrayBrace cid)
      '{' : rest -> do
        (body, after) <- splitDirective rest
        value <- directive body
        (value ++) <$> go after
      c : rest -> (c :) <$> go rest

    splitDirective r = case break (== '}') r of
      (body, '}' : after) -> Right (body, after)
      _ -> Left (NlUnterminatedBrace cid)

    directive body = case words body of
      [name, arg] | name == nlCellDirective -> cellValue (LeafId arg)
      _ -> Left (NlUnknownDirective cid body)

    cellValue lid = case lookup lid gamma of
      Nothing -> Left (NlCellLeafUndeclared cid lid)
      Just p -> case Cell.premiseCell p of
        Left _ -> Left (NlCellObligation cid lid)
        Right r -> Right (Cell.renderDecimal r)

