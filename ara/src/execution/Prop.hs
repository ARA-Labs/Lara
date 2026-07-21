-- Grounding: transcribed — verbatim from src/Lara/Prop.hs (repo), the implemented nf/≡
-- carve-out layer 1. Grounds C01. Do not edit here; edit the repo file.

-- | Ground propositions and the trusted identity relation @≡@ (spec §3, §3.2).
--
-- Propositions are __ground first-order atoms__: a predicate applied to ground
-- argument terms built from constructors and literals. There are no bound
-- variables at the proposition level (rule parameters are ground-substituted
-- away before a proposition is formed), so @≡@ needs no alpha-renaming and no
-- binder handling.
--
-- @≡@ is the trusted-base equality on propositions, so its definition is
-- deliberately minimal:
--
--   * it operates on __abstract syntax__, not surface text — the presentation
--     and JSON front ends both decode to this AST before @≡@ is applied, so
--     whitespace, field order, and encoding differences are already gone;
--   * it is @'nf' p '==' 'nf' q@, where the normal form 'nf' is literal
--     canonicalization ('canon') plus structural recursion;
--   * it does __not__ reorder arguments: no constructor or predicate is
--     associative, commutative, or symmetric in v0.1, so
--     @'Prop' \"p\" [a, b] '/=' 'Prop' \"p\" [b, a]@ unless @a '≡' b@.
--
-- The result is decidable, total, reflexive, symmetric, transitive, and linear
-- in term size — a trivial addition to the trusted base (spec result 11). The
-- @contrary@ matching (spec §4.1) and the @supports@ check (spec §3.1) both
-- reduce to '(===)'.
--
-- __Flip criterion__ (spec §3.2). If the corpus needs symmetric or AC
-- predicates (e.g. an unordered @distinct{a,b}@) or binders (quantified
-- propositions), extend 'nf' with argument sorting for the declared AC symbols
-- and de Bruijn indexing for binders, and re-establish the same properties.
-- That is a normalization extension, not a change to the
-- @p ≡ q  iff  nf p = nf q@ shape.
module Lara.Prop
  ( -- * Syntax
    Term (..)
  , Prop (..)
    -- * Normalization and identity
  , canonNum
  , nfTerm
  , nf
  , (===)
  , equiv
    -- * Rendering
  , prettyProp
  , prettyTerm
  ) where

-- | A ground term: a literal or a constructor applied to argument terms.
--
-- @g ::= k | k(g1, ..., gn)@ in the spec. A nullary constructor @k@ is
-- @'TCon' k []@; numeric and string literals are their own leaf constructors so
-- that 'canon' can normalize their surface forms.
data Term
  = -- | numeric literal, stored in surface form and normalized by 'canonNum'
    -- (e.g. @\"+2.1\"@ and @\"2.10\"@ both normalize to @\"2.1\"@)
    TNum String
  | -- | string literal (its decoded value; surface escaping is a codec concern,
    -- not a normalization step at this layer)
    TStr String
  | -- | constructor @k@ applied to zero or more arguments; @'TCon' k []@ is a
    -- nullary identifier constant such as @alice@
    TCon String [Term]
  deriving (Eq, Ord, Show)

-- | A proposition: a predicate applied to ground argument terms.
--
-- The nullary case @'Prop' p []@ is Phase 0's opaque, stable proposition
-- identifier (spec §3).
data Prop = Prop String [Term]
  deriving (Eq, Ord, Show)

-- ---------------------------------------------------------------------------
-- Normalization
-- ---------------------------------------------------------------------------

-- | Canonicalize a numeric literal's surface form to a single representative:
-- strip a leading @\'+\'@, drop insignificant leading and trailing zeros, and
-- drop a bare trailing @\'.\'@ or an all-zero fraction. A canonical zero is
-- unsigned. The function is total; input that is not a well-formed decimal is
-- returned structurally normalized but otherwise unchanged.
--
-- >>> canonNum "+2.1"
-- "2.1"
-- >>> canonNum "2.10"
-- "2.1"
-- >>> canonNum "-0.0"
-- "0"
canonNum :: String -> String
canonNum s = case s of
  '+' : rest -> unsigned rest
  '-' : rest -> let n = unsigned rest in if n == "0" then n else '-' : n
  _ -> unsigned s
  where
    unsigned t =
      let (intPart, dotFrac) = break (== '.') t
          intPart' = stripLeadingZeros intPart
          frac = case dotFrac of
            '.' : f -> stripTrailingZeros f
            _ -> ""
       in if null frac then intPart' else intPart' ++ '.' : frac

    -- drop leading zeros but keep at least one digit
    stripLeadingZeros ds = case dropWhile (== '0') ds of
      "" -> "0"
      ds' -> ds'

    stripTrailingZeros = reverse . dropWhile (== '0') . reverse

-- | Canonicalize an identifier (constructor or predicate name).
--
-- The spec's 'canon' applies Unicode NFC here. v0.1 leaves identifiers
-- byte-for-byte: NFC is the documented extension point, and pulling a Unicode
-- normalizer into the trusted base is deferred until an identifier in the
-- corpus actually needs it. When it does, this is the single place to add it.
canonId :: String -> String
canonId = id

-- | The normal form of a term: 'canon' on each literal, structural recursion
-- into constructors, argument order preserved.
nfTerm :: Term -> Term
nfTerm (TNum s) = TNum (canonNum s)
nfTerm (TStr s) = TStr s
nfTerm (TCon k ts) = TCon (canonId k) (map nfTerm ts)

-- | The normal form of a proposition (spec §3.2):
--
-- > nf(pred(g1, ..., gn)) = pred(nf(g1), ..., nf(gn))
nf :: Prop -> Prop
nf (Prop p ts) = Prop (canonId p) (map nfTerm ts)

-- | The trusted identity relation: @p ≡ q  iff  nf p = nf q@, where @=@ is
-- syntactic equality on the AST. Decidable, total, and an equivalence.
(===) :: Prop -> Prop -> Bool
p === q = nf p == nf q

infix 4 ===

-- | Prefix alias for '(===)'.
equiv :: Prop -> Prop -> Bool
equiv = (===)

-- ---------------------------------------------------------------------------
-- Rendering (for diagnostics and reports)
-- ---------------------------------------------------------------------------

-- | Render a proposition, e.g. @improves(M, accuracy, D)@.
prettyProp :: Prop -> String
prettyProp (Prop p []) = p
prettyProp (Prop p ts) = p ++ "(" ++ intercalateArgs ts ++ ")"

-- | Render a ground term.
prettyTerm :: Term -> String
prettyTerm (TNum s) = s
prettyTerm (TStr s) = show s
prettyTerm (TCon k []) = k
prettyTerm (TCon k ts) = k ++ "(" ++ intercalateArgs ts ++ ")"

intercalateArgs :: [Term] -> String
intercalateArgs = go
  where
    go [] = ""
    go [t] = prettyTerm t
    go (t : rest) = prettyTerm t ++ ", " ++ go rest
