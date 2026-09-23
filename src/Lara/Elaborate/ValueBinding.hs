-- | Consuming elaboration of @lara-syntax\@0.4@ value bindings.
--
-- The pass is deliberately one-way. It validates the authored binding table,
-- substitutes every program-side term occurrence simultaneously, resolves all
-- natural-language directives once, and clears the table. In particular, a
-- binding RHS is never rewritten through another binding.
module Lara.Elaborate.ValueBinding
  ( expandValueBindings
  ) where

import Data.List (find)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Lara.AST
import Lara.Elaborate.Error (ElabError (..))
import Lara.Prop (FunSym (..), Prop (..), Term (..), prettyTerm)
import Lara.Sigma (Sigma, lookupCon, sortCheckProp, sortOf)
import Lara.Syntax (nlCellDirective)
import qualified Lara.Strict.Cell as Cell

-- | Validate and consume one program's value-binding surface.
--
-- The returned 'Program' contains no bindings. Its declaration terms and prose
-- are the exact semantic presentation consumed by comparison expansion.
expandValueBindings :: Sigma -> Program -> Either ElabError Program
expandValueBindings sigma authored = do
  env <- bindingEnvironment sigma (programValueBindings authored)
  let substituted = authored {programDecls = map (substDecl env) (programDecls authored)}
  if Map.null env then Right () else validateClaimFormals sigma (programDecls substituted)
  expandedDecls <- expandDeclNls env (programDecls substituted)
  pure substituted {programValueBindings = [], programDecls = expandedDecls}

-- Name checks intentionally precede all RHS checks. This makes malformed
-- hand-built tables fail at their table boundary before any term traversal.
bindingEnvironment :: Sigma -> [ValueBinding] -> Either ElabError (Map ValueName Term)
bindingEnvironment sigma bindings = do
  env <- foldBindings Map.empty bindings
  case find ((== ValueName nlCellDirective) . valueName) bindings of
    Just binding -> Left (ReservedValueName (valueName binding))
    Nothing -> Right ()
  case find collides bindings of
    Just binding -> Left (ValueNameConstructorCollision (valueName binding))
    Nothing -> Right ()
  mapM_ validateRhs bindings
  pure env
  where
    foldBindings env [] = Right env
    foldBindings env (binding : rest)
      | Map.member (valueName binding) env =
          Left (DuplicateValueBinding (valueName binding))
      | otherwise =
          foldBindings
            (Map.insert (valueName binding) (valueTerm binding) env)
            rest
    collides binding =
      let ValueName name = valueName binding
       in case lookupCon sigma (FunSym name) of
            Just _ -> True
            Nothing -> False
    validateRhs binding =
      case sortOf sigma (valueTerm binding) of
        Left fault -> Left (ValueBindingSortError (valueName binding) fault)
        Right _ -> Right ()


-- A nullary constructor occurrence is the only substitution site. Returning
-- the mapped RHS directly (rather than recursively visiting it) is what makes
-- the environment simultaneous and non-recursive.
substTerm :: Map ValueName Term -> Term -> Term
substTerm env term = case term of
  TNum _ -> term
  TStr _ -> term
  TCon (FunSym name) [] ->
    case Map.lookup (ValueName name) env of
      Just replacement -> replacement
      Nothing -> term
  TCon headSym args -> TCon headSym (map (substTerm env) args)

substProp :: Map ValueName Term -> Prop -> Prop
substProp env (Prop predicate args) = Prop predicate (map (substTerm env) args)

substSupportTerm :: Map ValueName Term -> SupportTerm -> SupportTerm
substSupportTerm _ leaf@(SLeaf _) = leaf
substSupportTerm env rule@SRule {} =
  rule
    { srSubst = [(param, substTerm env term) | (param, term) <- srSubst rule]
    , srPremises = map (substSupportTerm env) (srPremises rule)
    , srDischarge =
        [ (question, substSupportTerm env support)
        | (question, support) <- srDischarge rule
        ]
    }

substArgInstantiation :: Map ValueName Term -> ArgInstantiation -> ArgInstantiation
substArgInstantiation env (ExplicitTheta term) =
  ExplicitTheta (substSupportTerm env term)
substArgInstantiation _ inferred@InferTheta {} = inferred

substDecl :: Map ValueName Term -> Decl -> Decl
substDecl env decl = case decl of
  DeclLeaf leaf -> DeclLeaf leaf {leafProp = substProp env (leafProp leaf)}
  DeclClaim claim -> DeclClaim claim {claimFormal = substProp env (claimFormal claim)}
  -- Value bindings rewrite explicit support terms. Inferred references name
  -- authored leaves/arguments, not value-bearing terms.
  DeclArg arg ->
    DeclArg arg {argInstantiation = substArgInstantiation env (argInstantiation arg)}
  DeclComparison comparison ->
    DeclComparison
      comparison
        { cmpConclusion = substProp env (cmpConclusion comparison)
        }
  DeclAttack _ -> decl
  DeclStatus _ -> decl
  DeclGroup _ -> decl

validateClaimFormals :: Sigma -> [Decl] -> Either ElabError ()
validateClaimFormals sigma = mapM_ validate
  where
    validate decl = case decl of
      DeclClaim claim ->
        case sortCheckProp sigma (claimFormal claim) of
          Just fault -> Left (ValueBindingClaimSortError (claimId claim) fault)
          Nothing -> Right ()
      _ -> Right ()

expandDeclNls :: Map ValueName Term -> [Decl] -> Either ElabError [Decl]
expandDeclNls env decls = mapM expandOne decls
  where
    gamma = [(leafId leaf, leafProp leaf) | DeclLeaf leaf <- decls]
    expandOne decl = case decl of
      DeclClaim claim -> do
        prose <- expandNl env gamma (claimId claim) (claimNl claim)
        pure (DeclClaim claim {claimNl = prose})
      DeclComparison comparison -> do
        let comparisonClaim = cmpClaim comparison
        prose <- expandNl env gamma (ccId comparisonClaim) (ccNlRaw comparisonClaim)
        pure
          ( DeclComparison
              comparison
                { cmpClaim = comparisonClaim {ccNlRaw = prose}
                }
          )
      _ -> Right decl

-- One left-to-right pass over the raw brace language. Escaped braces are emitted
-- as semantic prose and are never fed through this function a second time.
expandNl
  :: Map ValueName Term
  -> [(LeafId, Prop)]
  -> PropId
  -> String
  -> Either ElabError String
expandNl env gamma claim = go
  where
    go source = case source of
      [] -> Right []
      '{' : '{' : rest -> ('{' :) <$> go rest
      '}' : '}' : rest -> ('}' :) <$> go rest
      '}' : _ -> Left (NlStrayBrace claim)
      '{' : rest -> do
        (body, after) <- splitDirective rest
        value <- directive body
        (value ++) <$> go after
      char : rest -> (char :) <$> go rest

    splitDirective rest = case break (== '}') rest of
      (body, '}' : after) -> Right (body, after)
      _ -> Left (NlUnterminatedBrace claim)

    directive body = case words body of
      [name, arg] | name == nlCellDirective -> cellValue (LeafId arg)
      [name] | name /= nlCellDirective -> bindingValue (ValueName name)
      _ -> Left (NlUnknownDirective claim body)

    bindingValue name = case Map.lookup name env of
      Just term -> Right (prettyTerm term)
      Nothing -> Left (NlValueBindingMissing claim name)

    cellValue leafName = case lookup leafName gamma of
      Nothing -> Left (NlCellLeafUndeclared claim leafName)
      Just proposition -> case Cell.premiseCell proposition of
        Left _ -> Left (NlCellObligation claim leafName)
        Right rationalValue -> Right (Cell.renderDecimal rationalValue)
