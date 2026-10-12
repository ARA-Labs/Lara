module Lara.Process.Source.Provenance
  ( ProvenanceTable, buildProvenance, provenanceRows, checkedKeys, supportKeys
  , KindTable, buildKindTable, lookupKind, meetKinds, gradeNode
  ) where

import Control.Monad (unless)
import Numeric.Natural (Natural)
import qualified Lara.AST as A
import Lara.Policy (lookupRule)
import Lara.Prop (Prop, equiv)
import Lara.SupportTerm (instAPat)
import Lara.Process.Types (EvidenceKind (..), ProcessHistory, AdmissionBasis, Event (..), Stamped (..))
import Lara.Process.Audit.Types
import Lara.Process.Source
import Lara.Process.Source.Types
import Lara.Elaborate (acceptedSourceDeclared, acceptedSourceSemantic, acceptedSourcePolicy)

data ProvenanceTable = ProvenanceTable AcceptedObservation [(A.ArgId,[KindKey])]

provenanceRows :: ProvenanceTable -> [(A.ArgId,[KindKey])]
provenanceRows (ProvenanceTable _ rows) = rows
data Reference = Named A.ArgRef A.SupportTerm | Implicit Prop A.SupportTerm

data Prior = Prior A.ArgId A.SupportTerm Prop

supportKeys :: A.SupportTerm -> [KindKey]
supportKeys (A.SLeaf leaf) = [LeafKey leaf]
supportKeys (A.SRule rule _ premises discharges _ _) =
  MethodKey rule : concatMap supportKeys premises ++ concatMap (supportKeys . snd) discharges

-- Authored references retain identity even when distinct arguments inline to
-- the same core term. No checker or backend is invoked during this fold.
buildProvenance :: AcceptedObservation -> Either ProvenanceError ProvenanceTable
buildProvenance observation = do
  unless (length authored == length reconstructed) (Left ProvenanceShape)
  ProvenanceTable observation <$> build [] [] (zip authored reconstructed)
  where
    accepted = observationAcceptedSource observation
    semantic = acceptedSourceSemantic accepted
    policy = acceptedSourcePolicy accepted
    declared = acceptedSourceDeclared accepted
    leaves = [(A.leafId leaf,A.leafProp leaf) | A.DeclLeaf leaf <- A.programDecls semantic]
    authored = [argument | A.DeclArg argument <- A.programDecls semantic]
    reconstructed = A.unitArgs declared
    conclusion (A.SLeaf leaf) = maybe (Left ProvenanceShape) Right (lookup leaf leaves)
    conclusion (A.SRule rule theta _ _ _ _) = do
      scheme <- maybe (Left (ProvenanceMissingRule rule)) Right (lookupRule (A.unitRules declared) rule)
      maybe (Left ProvenanceImplicitMatch) Right (instAPat theta (A.ruleConclusion scheme))
    build _ table [] = Right table
    build priors table ((argument,(name,term)):rest) = do
      unless (A.argId argument == name) (Left ProvenanceShape)
      unless (name `notElem` map fst table) (Left (ProvenanceDuplicateArgument name))
      references <- instantiationReferences policy (A.argInstantiation argument) term
      dependencies <- fmap concat (traverse (resolve priors) references)
      inherited <- fmap concat (traverse (\ident -> maybe (Left (ProvenanceMissingArgument ident)) Right (lookup ident table)) dependencies)
      prop <- conclusion term
      build (priors ++ [Prior name term prop]) (table ++ [(name,ArgumentKey name : supportKeys term ++ inherited)]) rest
    resolve priors reference = case reference of
      Named (A.ArgRef name) retained -> case
        [(A.SLeaf leaf,Nothing) | (leaf@(A.LeafId text),_) <- leaves,text == name]
        ++ [(term,Just argument) | Prior argument@(A.ArgId text) term _ <- priors,text == name] of
          [(term,origin)] | term == retained -> Right (maybe [] (:[]) origin)
          [_] -> Left ProvenanceShape
          _ -> Left (ProvenanceUnresolvedReference (A.ArgRef name))
      Implicit ground retained -> case
        [(A.SLeaf leaf,Nothing) | (leaf,prop) <- leaves,equiv prop ground]
        ++ [(term,Just argument) | Prior argument term prop <- priors,equiv prop ground] of
          [(term,origin)] | term == retained -> Right (maybe [] (:[]) origin)
          [_] -> Left ProvenanceShape
          _ -> Left ProvenanceImplicitMatch

instantiationReferences :: A.Policy -> A.ArgInstantiation -> A.SupportTerm -> Either ProvenanceError [Reference]
instantiationReferences policy (A.ExplicitTheta authored) retained = termReferences policy authored retained
instantiationReferences _ (A.InferTheta rule refs ds _ _) (A.SRule rule' _ premises discharges _ _) = do
  unless (rule == rule') (Left ProvenanceShape)
  ps <- namedReferences refs premises
  qs <- namedDischarges ds discharges
  pure (ps ++ qs)
instantiationReferences _ _ _ = Left ProvenanceShape

namedReferences :: [A.ArgRef] -> [A.SupportTerm] -> Either ProvenanceError [Reference]
namedReferences [] [] = Right []
namedReferences (ref:refs) (term:terms) = (Named ref term :) <$> namedReferences refs terms
namedReferences _ _ = Left ProvenanceShape
namedDischarges :: [(A.QuestionId,A.ArgRef)] -> [(A.QuestionId,A.SupportTerm)] -> Either ProvenanceError [Reference]
namedDischarges [] [] = Right []
namedDischarges ((q,ref):refs) ((q',term):terms) = do
  unless (q == q') (Left ProvenanceShape)
  (Named ref term :) <$> namedDischarges refs terms
namedDischarges _ _ = Left ProvenanceShape

termReferences :: A.Policy -> A.SupportTerm -> A.SupportTerm -> Either ProvenanceError [Reference]
termReferences _ (A.SLeaf leaf) (A.SLeaf leaf')
  | leaf == leaf' = Right []
termReferences policy (A.SRule rule _ ps ds _ _) (A.SRule rule' theta ps' ds' _ _) = do
  unless (rule == rule') (Left ProvenanceShape)
  discharges <- explicitDischarges ds ds'
  premises <- case ps of
    [] -> do
      scheme <- maybe (Left (ProvenanceMissingRule rule)) Right (lookupRule (A.policyRules policy) rule)
      implicitReferences theta (A.rulePremises scheme) ps'
    _ -> explicitPremises policy ps ps'
  pure (premises ++ discharges)
termReferences _ _ _ = Left ProvenanceShape
explicitPremises :: A.Policy -> [A.SupportTerm] -> [A.SupportTerm] -> Either ProvenanceError [Reference]
explicitPremises _ [] [] = Right []
explicitPremises policy (a:as) (b:bs) = (++) <$> termReferences policy a b <*> explicitPremises policy as bs
explicitPremises _ _ _ = Left ProvenanceShape
implicitReferences :: A.Subst -> [A.AtomPat] -> [A.SupportTerm] -> Either ProvenanceError [Reference]
implicitReferences _ [] [] = Right []
implicitReferences theta (pattern':patterns) (term:terms) = do
  ground <- maybe (Left ProvenanceImplicitMatch) Right (instAPat theta pattern')
  (Implicit ground term :) <$> implicitReferences theta patterns terms
implicitReferences _ _ _ = Left ProvenanceShape
explicitDischarges :: [(A.QuestionId,A.SupportTerm)] -> [(A.QuestionId,A.SupportTerm)] -> Either ProvenanceError [Reference]
explicitDischarges [] [] = Right []
explicitDischarges ((q,A.SLeaf (A.LeafId ref)):refs) ((q',term):terms) = do
  unless (q == q') (Left ProvenanceShape)
  (Named (A.ArgRef ref) term :) <$> explicitDischarges refs terms
explicitDischarges _ _ = Left ProvenanceShape

checkedKeys :: ProvenanceTable -> Natural -> Either ProvenanceError [KindKey]
checkedKeys (ProvenanceTable observation rows) node = case atNatural (observationNames observation) node of
  Nothing -> Left (ProvenanceMissingNode node)
  Just argument -> maybe (Left (ProvenanceMissingArgument argument)) Right (lookup argument rows)
atNatural :: [a] -> Natural -> Maybe a
atNatural [] _ = Nothing
atNatural (x:_) 0 = Just x
atNatural (_:xs) n = atNatural xs (n-1)

data KindTable = KindTable SourceInput ProvenanceTable [(KindKey,(EvidenceKind,Bool))]
buildKindTable :: SourceInput -> ProvenanceTable -> ProcessHistory -> [KindSpec] -> [CaptureAssumption]
  -> [AdmissionBasis] -> [KindKey] -> [KindKey] -> KindTable
buildKindTable source provenance history specs assumptions admitted hypothetical conditional =
  KindTable source provenance [(kindKey spec,(min (kindUpper spec) (min (cap spec) (conditionalCap (kindKey spec))),True)) |
    spec <- specs,kindSource spec == source]
  where
    conditionalCap key = if key `elem` conditional then Conditional else Observed
    cap spec
      | kindKey spec `elem` hypothetical = Hypothetical
      | any (\(ident,key) -> kindAssumption spec == Just ident && kindKey spec == key) matchingAssumptions = Observed
      | otherwise = Conditional
    matchingAssumptions =
      [(captureId assumption,captureKey assumption) | assumption <- assumptions,
        captureSource assumption == source, captureEvent assumption `elem` history,
        captureBasis assumption `elem` admitted,
        case stampedEvent (captureEvent assumption) of
          Run run _ _ _ _ -> run == captureRun assumption
          Result run _ -> run == captureRun assumption
          _ -> False]
lookupKind :: KindTable -> KindKey -> (EvidenceKind,Bool)
lookupKind (KindTable _ _ rows) key = maybe (Hypothetical,False) id (lookup key rows)
meetKinds :: [(EvidenceKind,Bool)] -> (EvidenceKind,Bool)
meetKinds = foldr (\(kind,known) (rest,complete) -> (min kind rest,known && complete)) (Observed,True)
gradeNode :: KindTable -> Natural -> Either ProvenanceError (EvidenceKind,Bool)
gradeNode kinds@(KindTable _ provenance _) node =
  meetKinds . map (lookupKind kinds) <$> checkedKeys provenance node
