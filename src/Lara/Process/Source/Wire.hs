{-# LANGUAGE FlexibleInstances #-}
module Lara.Process.Source.Wire
  ( decodeSource, encodeSource, decodeFragment, encodeFragment
  , decodeProp, encodeProp, decodeReplay, encodeReplay, decodeCapture, encodeCapture
  , encodeLeafKind, decodeLeafKind, encodeProvenance, decodeProvenance
  ) where

import Control.Monad (unless)
import Lara.AST
import Lara.Prop (Prop (..), Term (..))
import Lara.Sigma
import Lara.Strict (SExpr (..))
import Lara.Evidence.Types
import Lara.Evidence.Registry (TypedObject (..))
import Lara.Evidence.CSV (CsvTable (..))
import Lara.Evidence.JSON (JsonValue (..))
import qualified Lara.Process.Wire as W
import qualified Lara.Process.Source.Types as T

-- This intermediate tree is private to the codec. Runtime values are typed ASTs.
data P = Str String | Int Integer | Node String [P] deriving (Eq, Show)
type Result = Either W.Error
bad :: Result a
bad = W.bad "malformed source presentation constructor"
class Codec a where
  enc :: a -> P
  dec :: P -> Result a
str :: (String -> a) -> P -> Result a
str f (Str s) = Right (f s)
str _ _ = bad
list :: (a -> P) -> [a] -> P
list f = Node "l" . map f
unlist :: (P -> Result a) -> P -> Result [a]
unlist f (Node "l" xs) = traverse f xs
unlist _ _ = bad
pair :: (a -> P) -> (b -> P) -> (a,b) -> P
pair f g (a,b) = Node "p" [f a,g b]
unpair :: (P -> Result a) -> (P -> Result b) -> P -> Result (a,b)
unpair f g (Node "p" [a,b]) = (,) <$> f a <*> g b
unpair _ _ _ = bad
optional :: (a -> P) -> Maybe a -> P
optional _ Nothing = Node "no" []
optional f (Just a) = Node "so" [f a]
unoptional :: (P -> Result a) -> P -> Result (Maybe a)
unoptional _ (Node "no" []) = Right Nothing
unoptional f (Node "so" [a]) = Just <$> f a
unoptional _ _ = bad
word :: Eq a => [(a,String)] -> a -> P
word table a = case lookup a table of Just s -> Node s []; Nothing -> error "closed source vocabulary"
unword :: [(a,String)] -> P -> Result a
unword table (Node s []) = maybe bad Right (lookup s [(b,a) | (a,b) <- table])
unword _ _ = bad
signed :: P -> Result Integer
signed (Int n) = Right n
signed _ = bad
instance Codec String where enc = Str; dec = str id
instance Codec Bool where enc = word [(True,"true"),(False,"false")]; dec = unword [(True,"true"),(False,"false")]
instance Codec LeafKind where enc = word leafKinds; dec = unword leafKinds
leafKinds :: [(LeafKind, String)]
leafKinds = [(Observed,"observed"),(Attested,"attested"),(Assumed,"assumed"),(Certified,"certified")]
instance Codec Provenance where
  enc User = Node "user" []; enc AiExecuted = Node "ai" []; enc (Checker n v) = Node "checker" [Str n,Str v]
  dec (Node "user" []) = Right User; dec (Node "ai" []) = Right AiExecuted; dec (Node "checker" [Str n,Str v]) = Right (Checker n v); dec _ = bad
instance Codec AuditStatus where enc = word audits; dec = unword audits
audits :: [(AuditStatus, String)]
audits = [(Unreviewed,"unreviewed"),(Reviewed,"reviewed"),(Disputed,"disputed")]
instance Codec Mode where enc = word modes; dec = unword modes
modes :: [(Mode, String)]
modes = [(Strict,"strict"),(Defeasible,"defeasible")]
instance Codec Necessity where enc = word necessities; dec = unword necessities
necessities :: [(Necessity, String)]
necessities = [(Mandatory,"mandatory"),(Optional,"optional")]
instance Codec Admission where enc = word admissions; dec = unword admissions
admissions :: [(Admission, String)]
admissions = [(Admit,"admit"),(Quarantine,"quarantine"),(Reject,"reject")]
instance Codec GroupConflictMode where enc = word groups; dec = unword groups
groups :: [(GroupConflictMode, String)]
groups = [(QuarantineOnConflict,"gq"),(RejectOnConflict,"gr")]
instance Codec Polarity where enc = word polarities; dec = unword polarities
polarities :: [(Polarity, String)]
polarities = [(HigherIsBetter,"hib"),(LowerIsBetter,"lib")]
instance Codec Relation where enc = word relations; dec = unword relations
relations :: [(Relation, String)]
relations = [(StrictlyBetter,"sb"),(AtLeastAsGood,"alag")]
instance Codec LeafCheckerId where enc = Node . checkerText <*> const []; dec (Node s []) = maybe bad Right (parseChecker s); dec _ = bad
instance Codec TermEncoding where enc = Node . encodingText <*> const []; dec (Node s []) = maybe bad Right (parseEncoding s); dec _ = bad
instance Codec CheckerVersion where enc (CheckerVersion v) = Int v; dec (Int v) = Right (CheckerVersion v); dec _ = bad
instance Codec Sort where
  enc SortNum = Node "sort-num" []; enc SortStr = Node "sort-str" []; enc (SortDecl (SortName n)) = Node "sort-decl" [Str n]
  dec (Node "sort-num" []) = Right SortNum; dec (Node "sort-str" []) = Right SortStr; dec (Node "sort-decl" [Str n]) = Right (SortDecl (SortName n)); dec _ = bad
instance Codec ConSig where
  enc (ConSig (FunSym n) args result) = Node "con-sig" [Str n,list enc args,enc result]
  dec (Node "con-sig" [Str n,args,result]) = ConSig (FunSym n) <$> unlist dec args <*> dec result; dec _ = bad
instance Codec PredSig where
  enc (PredSig (Pred n) args) = Node "pred-sig" [Str n,list enc args]
  dec (Node "pred-sig" [Str n,args]) = PredSig (Pred n) <$> unlist dec args; dec _ = bad
instance Codec Sigma where
  enc (Sigma sorts cons preds) = Node "sigma" [list (\(SortName s) -> Str s) sorts,list enc cons,list enc preds]
  dec (Node "sigma" [sorts,cons,preds]) = Sigma <$> unlist (str SortName) sorts <*> unlist dec cons <*> unlist dec preds; dec _ = bad
instance Codec Term where
  enc (TNum n) = Node "tn" [Str n]; enc (TStr s) = Node "ts" [Str s]; enc (TCon (FunSym k) ts) = Node "tc" (Str k : map enc ts)
  dec (Node "tn" [Str n]) = Right (TNum n); dec (Node "ts" [Str s]) = Right (TStr s); dec (Node "tc" (Str k : ts)) = TCon (FunSym k) <$> traverse dec ts; dec _ = bad
instance Codec Prop where
  enc (Prop (Pred p) ts) = Node "atom" (Str p : map enc ts)
  dec (Node "atom" (Str p : ts)) = Prop (Pred p) <$> traverse dec ts; dec _ = bad
instance Codec Pat where
  enc (PVar (Param v)) = Node "pv" [Str v]; enc (PLit t) = Node "pl" [enc t]; enc (PCon (FunSym k) ps) = Node "pc" (Str k : map enc ps)
  dec (Node "pv" [Str v]) = Right (PVar (Param v)); dec (Node "pl" [t]) = PLit <$> dec t; dec (Node "pc" (Str k : ps)) = PCon (FunSym k) <$> traverse dec ps; dec _ = bad
instance Codec AtomPat where
  enc (AtomPat (Pred p) ps) = Node "apat" (Str p : map enc ps)
  dec (Node "apat" (Str p : ps)) = AtomPat (Pred p) <$> traverse dec ps; dec _ = bad

-- Opaque payload trees are adapted once, without textual parsing.
payload :: SExpr -> P
payload (SAtom s) = Str s
payload (SList []) = Node "" []
payload (SList (SAtom tag : xs)) = Node tag (map payload xs)
payload (SList xs) = Node "" (map payload xs)
unpayload :: P -> SExpr
unpayload (Str s) = SAtom s
unpayload (Int n) = SAtom (show n)
unpayload (Node tag xs) = SList (SAtom tag : map unpayload xs)
instance Codec Cert where
  enc (Cert (BackendId b) v (TheoryDigest t) p) = Node "cert" [Str b,Int (toInteger v),Str t,payload p]
  dec (Node "cert" [Str b,v,Str t,p]) = Cert (BackendId b) <$> signed v <*> pure (TheoryDigest t) <*> pure (unpayload p); dec _ = bad
instance Codec Assurance where
  enc AssuranceNone = Node "an" []; enc AssuranceTrusted = Node "at" []; enc (AssuranceCert c) = Node "ac" [enc c]
  dec (Node "an" []) = Right AssuranceNone; dec (Node "at" []) = Right AssuranceTrusted; dec (Node "ac" [c]) = AssuranceCert <$> dec c; dec _ = bad
instance Codec SupportTerm where
  enc (SLeaf (LeafId l)) = Node "sl" [Str l]
  enc (SRule (RuleId r) s ps ds hs a) = Node "sr" [Str r,list (pair (\(Param x) -> Str x) enc) s,Node "prems" (map enc ps),Node "dis" [Node "d" [Str q,enc w] | (QuestionId q,w) <- ds],list (\(ObligationId o) -> Str o) hs,enc a]
  dec (Node "sl" [Str l]) = Right (SLeaf (LeafId l))
  dec (Node "sr" [Str r,s,Node "prems" ps,Node "dis" ds,hs,a]) = SRule (RuleId r) <$> unlist (unpair (str Param) dec) s <*> traverse dec ps <*> traverse discharge ds <*> unlist (str ObligationId) hs <*> dec a
    where discharge (Node "d" [q,w]) = (,) <$> str QuestionId q <*> dec w; discharge _ = bad
  dec _ = bad
instance Codec CsvSelector where
  enc (CsvSelector (ColumnName c) e) = Node "select" [Str c,enc e]
  dec (Node "select" [Str c,e]) = CsvSelector (ColumnName c) <$> dec e; dec _ = bad
instance Codec JsonSelector where
  enc (JsonSelector p e) = Node "select" [list (\(JsonToken t) -> Str t) p,enc e]
  dec (Node "select" [p,e]) = JsonSelector <$> unlist (str JsonToken) p <*> dec e; dec _ = bad
instance Codec ExtractionRequest where
  enc (CsvRowRequest v (ObjectId o) (ColumnName k) raw sels (Pred p)) = Node "csv-row" [enc v,Str o,Str k,Str raw,list enc sels,Str p]
  enc (JsonPointerRequest v (ObjectId o) sels (Pred p)) = Node "json-pointer" [enc v,Str o,list enc sels,Str p]
  dec (Node "csv-row" [v,Str o,Str k,Str raw,sels,Str p]) = CsvRowRequest <$> dec v <*> pure (ObjectId o) <*> pure (ColumnName k) <*> pure raw <*> unlist dec sels <*> pure (Pred p)
  dec (Node "json-pointer" [v,Str o,sels,Str p]) = JsonPointerRequest <$> dec v <*> pure (ObjectId o) <*> unlist dec sels <*> pure (Pred p); dec _ = bad
instance Codec Leaf where
  enc (Leaf (LeafId i) p k v refs ex) = Node "leaf" [Str i,enc p,enc k,enc v,list (\(SourceRef s) -> Str s) refs,optional enc ex]
  dec (Node "leaf" [i,p,k,v,refs,ex]) = Leaf <$> str LeafId i <*> dec p <*> dec k <*> dec v <*> unlist (str SourceRef) refs <*> unoptional dec ex; dec _ = bad
instance Codec Binding where
  enc (Binding a r s) = Node "bind" [Str a,Str r,enc s]
  dec (Node "bind" [Str a,Str r,s]) = Binding a r <$> dec s; dec _ = bad
instance Codec Claim where
  enc (Claim (PropId i) nl f b) = Node "claim" [Str i,Str nl,enc f,enc b]
  dec (Node "claim" [i,Str nl,f,b]) = Claim <$> str PropId i <*> pure nl <*> dec f <*> dec b; dec _ = bad
instance Codec Question where
  enc (Question (QuestionId i) a n) = Node "q" [Str i,enc a,enc n]
  dec (Node "q" [i,a,n]) = Question <$> str QuestionId i <*> dec a <*> dec n; dec _ = bad
instance Codec CertRef where
  enc (CertRef (BackendId b) v (TheoryDigest t)) = Node "cref" [Str b,Int (toInteger v),Str t]
  dec (Node "cref" [b,v,t]) = CertRef <$> str BackendId b <*> signed v <*> str TheoryDigest t; dec _ = bad
instance Codec Rule where
  enc (Rule (RuleId i) ps m prems labels c a certs qs) = Node "rule" [Str i,list (\(Param p) -> Str p) ps,enc m,list enc prems,list (optional (\(PremiseLabel l) -> Str l)) labels,enc c,enc a,list enc certs,list enc qs]
  dec (Node "rule" [i,ps,m,prems,labels,c,a,certs,qs]) = Rule <$> str RuleId i <*> unlist (str Param) ps <*> dec m <*> unlist dec prems <*> unlist (unoptional (str PremiseLabel)) labels <*> dec c <*> dec a <*> unlist dec certs <*> unlist dec qs; dec _ = bad
instance Codec Contrary where enc (Contrary l r) = Node "contra" [enc l,enc r]; dec (Node "contra" [l,r]) = Contrary <$> dec l <*> dec r; dec _ = bad
instance Codec Exception where enc (Exception (RuleId r) a) = Node "exc" [Str r,enc a]; dec (Node "exc" [r,a]) = Exception <$> str RuleId r <*> dec a; dec _ = bad
instance Codec DupGroup where enc (DupGroup (GroupId i) ms) = Node "group" [Str i,list (\(LeafId l) -> Str l) ms]; dec (Node "group" [i,ms]) = DupGroup <$> str GroupId i <*> unlist (str LeafId) ms; dec _ = bad
instance Codec Measurand where enc (Measurand (MeasurandId i) s p) = Node "meas" [Str i,enc s,optional enc p]; dec (Node "meas" [i,s,p]) = Measurand <$> str MeasurandId i <*> dec s <*> unoptional dec p; dec _ = bad
instance Codec ComparisonScheme where enc (ComparisonScheme r p (RuleId a) (RuleId b)) = Node "cscheme" [enc r,enc p,Str a,Str b]; dec (Node "cscheme" [r,p,a,b]) = ComparisonScheme <$> dec r <*> dec p <*> str RuleId a <*> str RuleId b; dec _ = bad
instance Codec Policy where
  enc (Policy (PolicyId i) s rs cs es am ts gm ms sch ec) = Node "policy" [Str i,enc s,list enc rs,list enc cs,list enc es,list (pair (pair enc enc) enc) am,list (pair (\(TheoryDigest t) -> Str t) (list enc)) ts,enc gm,list enc ms,list enc sch,list (pair enc enc) ec]
  dec (Node "policy" [i,s,rs,cs,es,am,ts,gm,ms,sch,ec]) = Policy <$> str PolicyId i <*> dec s <*> unlist dec rs <*> unlist dec cs <*> unlist dec es <*> unlist (unpair (unpair dec dec) dec) am <*> unlist (unpair (str TheoryDigest) (unlist dec)) ts <*> dec gm <*> unlist dec ms <*> unlist dec sch <*> unlist (unpair dec dec) ec; dec _ = bad
instance Codec SurfaceStep where enc (StepIndex i) = Node "ssi" [Int i]; enc (StepName s) = Node "ssn" [Str s]; dec (Node "ssi" [i]) = StepIndex <$> signed i; dec (Node "ssn" [Str s]) = Right (StepName s); dec _ = bad
instance Codec SurfaceAttack where
  enc (SRebut (ArgId a) (ArgId b)) = Node "sreb" [Str a,Str b]
  enc (SUndercut (ArgId a) (ArgId b) p) = Node "sunc" [Str a,Str b,list enc p]
  enc (SUndermine (ArgId a) (ArgId b) p) = Node "sunm" [Str a,Str b,list enc p]
  dec (Node "sreb" [a,b]) = SRebut <$> str ArgId a <*> str ArgId b
  dec (Node "sunc" [a,b,p]) = SUndercut <$> str ArgId a <*> str ArgId b <*> unlist dec p
  dec (Node "sunm" [a,b,p]) = SUndermine <$> str ArgId a <*> str ArgId b <*> unlist dec p; dec _ = bad
instance Codec ChallengeTarget where
  enc (ChallengesQuestion (QuestionId q) (ArgId a)) = Node "chq" [Str q,Str a]; enc (ChallengesLeaf (LeafId l)) = Node "chl" [Str l]
  dec (Node "chq" [q,a]) = ChallengesQuestion <$> str QuestionId q <*> str ArgId a; dec (Node "chl" [l]) = ChallengesLeaf <$> str LeafId l; dec _ = bad
instance Codec ArgConcl where
  enc (SupportsClaim (PropId c)) = Node "sc" [Str c]; enc (SupportsDerived (PropId c)) = Node "sd" [Str c]; enc (Challenges t) = Node "ch" [enc t]
  dec (Node "sc" [c]) = SupportsClaim <$> str PropId c; dec (Node "sd" [c]) = SupportsDerived <$> str PropId c; dec (Node "ch" [t]) = Challenges <$> dec t; dec _ = bad
instance Codec ArgInstantiation where
  enc (ExplicitTheta t) = Node "et" [enc t]
  enc (InferTheta (RuleId r) refs ds os a) = Node "it" [Str r,list (\(ArgRef n) -> Str n) refs,list (pair (\(QuestionId q) -> Str q) (\(ArgRef n) -> Str n)) ds,list (\(ObligationId o) -> Str o) os,enc a]
  dec (Node "et" [t]) = ExplicitTheta <$> dec t
  dec (Node "it" [r,refs,ds,os,a]) = InferTheta <$> str RuleId r <*> unlist (str ArgRef) refs <*> unlist (unpair (str QuestionId) (str ArgRef)) ds <*> unlist (str ObligationId) os <*> dec a; dec _ = bad
instance Codec Arg where enc (Arg (ArgId i) c t) = Node "arg" [Str i,enc c,enc t]; dec (Node "arg" [i,c,t]) = Arg <$> str ArgId i <*> dec c <*> dec t; dec _ = bad
instance Codec ComparisonClaim where enc (ComparisonClaim (PropId i) nl b) = Node "cclaim" [Str i,Str nl,enc b]; dec (Node "cclaim" [i,Str nl,b]) = ComparisonClaim <$> str PropId i <*> pure nl <*> dec b; dec _ = bad
instance Codec Comparison where
  enc (Comparison c (MeasurandId m) (DatasetId d) r (ArgId rc) (ArgId br) (LeafId rs) (LeafId bl) (LeafId bd) cl sp) = Node "cmp" [enc c,Str m,Str d,enc r,Str rc,Str br,Str rs,Str bl,Str bd,enc cl,optional (\(PropId p) -> Str p) sp]
  dec (Node "cmp" [c,m,d,r,rc,br,rs,bl,bd,cl,sp]) = Comparison <$> dec c <*> str MeasurandId m <*> str DatasetId d <*> dec r <*> str ArgId rc <*> str ArgId br <*> str LeafId rs <*> str LeafId bl <*> str LeafId bd <*> dec cl <*> unoptional (str PropId) sp; dec _ = bad
instance Codec Decl where
  enc (DeclLeaf l) = Node "dl" [enc l]; enc (DeclClaim c) = Node "dc" [enc c]; enc (DeclArg a) = Node "da" [enc a]; enc (DeclAttack k) = Node "dk" [enc k]; enc (DeclStatus (PropId p)) = Node "ds" [Str p]; enc (DeclGroup g) = Node "dg" [enc g]; enc (DeclComparison c) = Node "dm" [enc c]
  dec (Node "dl" [l]) = DeclLeaf <$> dec l; dec (Node "dc" [c]) = DeclClaim <$> dec c; dec (Node "da" [a]) = DeclArg <$> dec a; dec (Node "dk" [k]) = DeclAttack <$> dec k; dec (Node "ds" [p]) = DeclStatus <$> str PropId p; dec (Node "dg" [g]) = DeclGroup <$> dec g; dec (Node "dm" [c]) = DeclComparison <$> dec c; dec _ = bad
instance Codec ValueBinding where enc (ValueBinding (ValueName n) t) = Node "value-binding" [Str n,enc t]; dec (Node "value-binding" [n,t]) = ValueBinding <$> str ValueName n <*> dec t; dec _ = bad
instance Codec Program where
  enc (Program a (Digest d) (PolicyId p) bs vs ds) = Node "program" [Str a,Str d,Str p,list (pair (\(BackendId b) -> Str b) Str) bs,list enc vs,list enc ds]
  dec (Node "program" [Str a,d,p,bs,vs,ds]) = Program a <$> str Digest d <*> str PolicyId p <*> unlist (unpair (str BackendId) (str id)) bs <*> unlist dec vs <*> unlist dec ds; dec _ = bad

encodeP :: P -> SExpr
encodeP (Str s) = W.tagged "string" [SAtom s]
encodeP (Int n) | n >= 0 = W.tagged "integer-natural" [SAtom (show n)]
                | otherwise = W.tagged "integer-negative-successor" [SAtom (show (-n-1))]
encodeP (Node t xs) = W.tagged "node" [SAtom t,children xs]
  where children [] = W.tagged "nil" []; children (x:rest) = W.tagged "cons" [encodeP x,children rest]
decodeP :: SExpr -> Result P
decodeP (SList [SAtom "string",SAtom s]) = Right (Str s)
decodeP (SList [SAtom "integer-natural",n]) = Int . toInteger <$> W.decodeNat n
decodeP (SList [SAtom "integer-negative-successor",n]) = Int . (\m -> -toInteger m-1) <$> W.decodeNat n
decodeP (SList [SAtom "node",SAtom t,xs]) = Node t <$> children xs
  where children (SList [SAtom "nil"]) = Right []; children (SList [SAtom "cons",x,rest]) = (:) <$> decodeP x <*> children rest; children _ = bad
decodeP _ = bad
canonical :: Eq a => (a -> SExpr) -> (SExpr -> Result a) -> SExpr -> Result a
canonical encode decode tree = do
  value <- decode tree
  unless (encode value == tree) (W.bad "non-canonical source encoding")
  pure value
encodeProp :: Prop -> SExpr
encodeProp = encodeP . enc
decodeProp :: SExpr -> Result Prop
decodeProp = canonical encodeProp (decodeP >=> dec)
  where (>=>) f g x = f x >>= g
encodeFragment :: T.Fragment -> SExpr
encodeFragment fragment = W.tagged "checked-fragment"
  [SAtom "1",encodeP (Node "l" (mapCertificatePayloads
    (\coordinate original -> maybe original fromCertificate (lookup coordinate (T.fragmentCertificatePayloads fragment)))
    (map enc (T.fragmentDecls fragment))))]
decodeFragment :: SExpr -> Result T.Fragment
decodeFragment = canonical encodeFragment raw
  where
    raw (SList [SAtom "checked-fragment",SAtom "1",ds]) = do
      tree <- decodeP ds
      declarations <- unlist dec tree
      case tree of
        Node "l" children -> either W.bad Right
          (T.mkFragmentWithPayloads declarations (certificatePresentations children))
        _ -> bad
    raw _ = bad
encodeReplay :: T.ReplayIdentity -> SExpr
encodeReplay (T.ReplayIdentity (T.CoreVersion c) (PolicyId p) bs ts (Digest a)) = W.tagged "replay" [SAtom c,SAtom p,SList (map backend bs),SList [SAtom t | TheoryDigest t <- ts],SAtom a]
  where backend (T.BackendIdentity (BackendId b) (T.BackendVersion v)) = W.tagged "backend" [SAtom b,SAtom v]
decodeReplay :: SExpr -> Result T.ReplayIdentity
decodeReplay (SList [SAtom "replay",SAtom c,SAtom p,SList bs,SList ts,SAtom a]) = T.ReplayIdentity (T.CoreVersion c) (PolicyId p) <$> traverse backend bs <*> traverse (fmap TheoryDigest . W.decodeText) ts <*> pure (Digest a)
  where backend (SList [SAtom "backend",SAtom b,SAtom v]) = Right (T.BackendIdentity (BackendId b) (T.BackendVersion v)); backend _ = bad
decodeReplay _ = bad
encodeMeta :: T.ObjectMeta -> SExpr
encodeMeta (T.ObjectMeta (ObjectId i) p n d) = W.tagged "object" [SAtom i,SAtom p,W.encodeNat n,SAtom d]
decodeMeta :: SExpr -> Result T.ObjectMeta
decodeMeta (SList [SAtom "object",SAtom i,SAtom p,n,SAtom d]) = T.ObjectMeta (ObjectId i) p <$> W.decodeNat n <*> pure d
decodeMeta _ = bad
encodeJson :: JsonValue -> SExpr
encodeJson (JsonObject es) = W.tagged "object" [entries es]
  where entries [] = SList []; entries ((JsonToken k,v):rest) = SList [SAtom k,encodeJson v,entries rest]
encodeJson (JsonArray vs) = W.tagged "array" [values vs]
  where values [] = SList []; values (v:rest) = SList [encodeJson v,values rest]
encodeJson (JsonString s) = W.tagged "string" [SAtom s]
encodeJson (JsonNumber s) = W.tagged "number" [SAtom s]
encodeJson (JsonBool True) = SAtom "true"
encodeJson (JsonBool False) = SAtom "false"
encodeJson JsonNull = SAtom "null"
decodeJson :: SExpr -> Result JsonValue
decodeJson (SList [SAtom "object",es]) = JsonObject <$> entries es
  where entries (SList []) = Right []; entries (SList [SAtom k,v,rest]) = (:) <$> ((,) (JsonToken k) <$> decodeJson v) <*> entries rest; entries _ = bad
decodeJson (SList [SAtom "array",vs]) = JsonArray <$> values vs
  where values (SList []) = Right []; values (SList [v,rest]) = (:) <$> decodeJson v <*> values rest; values _ = bad
decodeJson (SList [SAtom "string",SAtom s]) = Right (JsonString s)
decodeJson (SList [SAtom "number",SAtom s]) = Right (JsonNumber s)
decodeJson (SAtom "true") = Right (JsonBool True)
decodeJson (SAtom "false") = Right (JsonBool False)
decodeJson (SAtom "null") = Right JsonNull
decodeJson _ = bad
encodeTyped :: TypedObject -> SExpr
encodeTyped (CsvPayload (CsvTable header rows)) = W.tagged "csv" [SList [SList [SAtom h | ColumnName h <- header],SList [SList (map SAtom row) | row <- rows]]]
encodeTyped (JsonPayload j) = W.tagged "json" [encodeJson j]
decodeTyped :: SExpr -> Result TypedObject
decodeTyped (SList [SAtom "csv",SList [SList header,SList rows]]) = CsvPayload <$> (CsvTable <$> traverse (fmap ColumnName . W.decodeText) header <*> traverse row rows)
  where row (SList cells) = traverse W.decodeText cells; row _ = bad
decodeTyped (SList [SAtom "json",j]) = JsonPayload <$> decodeJson j
decodeTyped _ = bad
encodeCapture :: T.EvidenceCapture -> SExpr
encodeCapture (T.EvidenceCapture snapshot manifest) = W.tagged "evidence" [SList (map entry snapshot),SList (map encodeMeta manifest)]
  where entry (ObjectId i,result) = SList [SAtom i,case result of Left reason -> W.tagged "failed" [SAtom reason]; Right (meta,p) -> W.tagged "captured" [SList [encodeMeta meta,encodeTyped p]]]
decodeCapture :: SExpr -> Result T.EvidenceCapture
decodeCapture (SList [SAtom "evidence",SList snapshot,SList manifest]) = T.EvidenceCapture <$> traverse entry snapshot <*> traverse decodeMeta manifest
  where
    entry (SList [SAtom i,result]) = (,) (ObjectId i) <$> capture result
    entry _ = bad
    capture (SList [SAtom "failed",SAtom reason]) = Right (Left reason)
    capture (SList [SAtom "captured",SList [meta,p]]) = Right <$> ((,) <$> decodeMeta meta <*> decodeTyped p)
    capture _ = bad
decodeCapture _ = bad
encodeSource :: T.SourceInput -> SExpr
encodeSource source = W.tagged "checked-source"
  [SAtom "1",SList [encodeP programTree,encodeP (enc (T.sourcePolicy source))],
    encodeReplay (T.sourceReplay source),case T.sourceCapture source of
      Nothing -> W.tagged "absent" []
      Just capture -> W.tagged "present" [encodeCapture capture]]
  where
    programTree = case enc (T.sourceProgram source) of
      Node "program" [a,d,p,bs,vs,Node "l" declarations] ->
        Node "program" [a,d,p,bs,vs,Node "l" (mapCertificatePayloads
          (\coordinate original -> maybe original fromCertificate (lookup coordinate (T.sourceCertificatePayloads source))) declarations)]
      tree -> tree
decodeSource :: SExpr -> Result T.SourceInput
decodeSource = canonical encodeSource raw
  where
    raw (SList [SAtom "checked-source",SAtom "1",SList [program,policy],replay,capture]) = do
      programTree <- decodeP program
      authored <- dec programTree
      authoredPolicy <- decodeP policy >>= dec
      identity <- decodeReplay replay
      evidence <- optionalCapture capture
      case programTree of
        Node "program" [_,_,_,_,_,Node "l" declarations] ->
          either W.bad Right (T.mkSourceInputWithPayloads authored authoredPolicy identity evidence (certificatePresentations declarations))
        _ -> bad
    raw _ = bad
    optionalCapture (SList [SAtom "absent"]) = Right Nothing
    optionalCapture (SList [SAtom "present",c]) = Just <$> decodeCapture c
    optionalCapture _ = bad

fromCertificate :: T.CertificatePayload -> P
fromCertificate (T.CertificateString s) = Str s
fromCertificate (T.CertificateInteger n) = Int n
fromCertificate (T.CertificateNode tag children) = Node tag (map fromCertificate children)
toCertificate :: P -> T.CertificatePayload
toCertificate (Str s) = T.CertificateString s
toCertificate (Int n) = T.CertificateInteger n
toCertificate (Node tag children) = T.CertificateNode tag (map toCertificate children)

certificatePresentations :: [P] -> [(T.CertificateCoordinate,T.CertificatePayload)]
certificatePresentations declarations = concat
  [argument index declaration | (index,declaration) <- zip [0..] declarations]
  where
    argument index (Node "da" [Node "arg" [_,_,Node "et" [term]]]) = supports index [] term
    argument index (Node "da" [Node "arg" [_,_,Node "it" [_,_,_,_,assurance]]]) = assured index [] assurance
    argument _ _ = []
    supports index path (Node "sr" [_,_,Node "prems" ps,Node "dis" ds,_,assurance]) =
      assured index path assurance
      ++ concat [supports index (path ++ [T.CertificatePremise n]) term | (n,term) <- zip [0..] ps]
      ++ concat [supports index (path ++ [T.CertificateDischarge n]) term | (n,Node "d" [_,term]) <- zip [0..] ds]
    supports _ _ _ = []
    assured index path (Node "ac" [Node "cert" [_,_,_,tree]]) =
      [(T.DeclarationCertificate index path,toCertificate tree)]
    assured _ _ _ = []

mapCertificatePayloads :: (T.CertificateCoordinate -> P -> P) -> [P] -> [P]
mapCertificatePayloads transform declarations =
  [argument index declaration | (index,declaration) <- zip [0..] declarations]
  where
    argument index (Node "da" [Node "arg" [name,conclusion,Node "et" [term]]]) =
      Node "da" [Node "arg" [name,conclusion,Node "et" [supports index [] term]]]
    argument index (Node "da" [Node "arg" [name,conclusion,Node "it" [r,refs,ds,hs,assurance]]]) =
      Node "da" [Node "arg" [name,conclusion,Node "it" [r,refs,ds,hs,assured index [] assurance]]]
    argument _ tree = tree
    supports index path (Node "sr" [r,s,Node "prems" ps,Node "dis" ds,hs,assurance]) =
      Node "sr" [r,s,Node "prems" [supports index (path ++ [T.CertificatePremise n]) term | (n,term) <- zip [0..] ps],
        Node "dis" [case entry of
          Node "d" [q,term] -> Node "d" [q,supports index (path ++ [T.CertificateDischarge n]) term]
          tree -> tree | (n,entry) <- zip [0..] ds],hs,assured index path assurance]
    supports _ _ tree = tree
    assured index path (Node "ac" [Node "cert" [b,v,t,tree]]) =
      Node "ac" [Node "cert" [b,v,t,transform (T.DeclarationCertificate index path) tree]]
    assured _ _ tree = tree

encodeLeafKind :: LeafKind -> SExpr
encodeLeafKind = encodeP . enc
decodeLeafKind :: SExpr -> Result LeafKind
decodeLeafKind = canonical encodeLeafKind (\tree -> decodeP tree >>= dec)
encodeProvenance :: Provenance -> SExpr
encodeProvenance = encodeP . enc
decodeProvenance :: SExpr -> Result Provenance
decodeProvenance = canonical encodeProvenance (\tree -> decodeP tree >>= dec)
