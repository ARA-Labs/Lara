-- | The certificate-family site enumerators (#125, split out of
-- "Lara.Mutate.Sites" once the family had its own vocabulary; see
-- @docs\/mutate-module-ownership-decision.md@).
--
-- Three operators strike an allowlisted certificate, at three different depths
-- of the strict-adapter pipeline:
--
-- > operator              what it corrupts              where it dies
-- > cert-theory-swap      the theory digest             allowlist (R7)
-- > cert-payload-tamper   the payload's structure       backend decoder (R13)
-- > cert-wrong-fraction   the payload's /value/         backend value recheck (R13)
--
-- The last two are deliberately near-duplicates: they differ only in whether
-- the mutant survives @'Lara.Strict.RA.decodeCert'@. That distinction is what
-- @test\/MutationSpec.hs@'s @prop_certWrongFractionDecodes@ pins, since the
-- manifest columns cannot express it.
--
-- The enumerators keep the ordering and self-gating invariants documented in
-- "Lara.Mutate.Sites"; the navigation helpers they run on live in
-- "Lara.Mutate.Sites.Nav".
module Lara.Mutate.Sites.Cert
  ( certTheorySwapSites
  , certPayloadSites
  , certWrongFractionSites
  , bumpWitness
  ) where

import Data.Ratio (denominator, numerator, (%))

import Lara.AST
import Lara.Diagnostics (Constituent (..))
import Lara.Strict (SExpr (..))
import Lara.Strict.Cell (parseCanonicalInt, parseCanonicalNat)
import Lara.Strict.RA (Tag (..), parseTag)

import Lara.Mutate (Expected (..))
import Lara.Mutate.Sites.Nav (rewriteArg, rewriteAt, ruleSites)

-- R7: point an allowlisted certificate at a theory digest no certifier lists.
certTheorySwapSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
certTheorySwapSites u =
  [ ( ExpectClass R7
    , CArgument ix
    , rewriteArg ix (rewriteAt pos swapTheory)
    )
  | (ix, pos, SRule _ _ _ _ _ (AssuranceCert _)) <- ruleSites u
  ]
  where
    swapTheory (SRule r theta ws d hs (AssuranceCert cert)) =
      SRule r theta ws d hs (AssuranceCert cert {certTheory = TheoryDigest "sha256:mut"})
    swapTheory t = t

-- R13: corrupt an allowlisted certificate's opaque payload (replay reject).
certPayloadSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
certPayloadSites u =
  [ ( ExpectClass R13
    , CArgument ix
    , rewriteArg ix (rewriteAt pos tamper)
    )
  | (ix, pos, SRule _ _ _ _ _ (AssuranceCert _)) <- ruleSites u
  ]
  where
    tamper (SRule r theta ws d hs (AssuranceCert cert)) =
      SRule r theta ws d hs (AssuranceCert cert {certPayload = SAtom "mut_corrupt"})
    tamper t = t

-- R13: a well-formed @ra\@1@ payload carrying the /wrong/ value.
--
-- Distinct from 'certPayloadSites' on purpose. That operator writes structural
-- garbage, which the backend decoder throws out — it exercises the decoder. This
-- one produces a payload that decodes cleanly (canonical numerals, positive
-- denominator, lowest terms) and is refused only by the /value recheck/ — the
-- only /mutation operator/ that reaches "plausible-looking but false
-- certificate". It is not the corpus's only such input: the hand-authored
-- @fixtures\/corpus\/ord-lt-boundary-reject.sexp@ is the @ord\@1@ analogue,
-- decoding cleanly and refused on value with @5 < 5 is false@
-- (@docs\/rejection-surface.md@, R13). What this operator adds is the /seeded/
-- one, derived from a real certificate rather than authored against it.
--
-- The @ra\@1@ wire form exists to make exactly this distinction: one wire form
-- per value, so a well-formed payload carrying a different value is a replay
-- rejection rather than a decode failure ("Lara.Strict.RA").
--
-- The mutant exercises the value recheck as a whole, not one branch of it: it
-- moves the witness and leaves the goal's claimed @C@ alone, so it trips both
-- 'Lara.Strict.RA.checkDrop' guards and merely reports the first. Isolating the
-- recomputation guard needs the goal moved alongside the witness, which a
-- payload-only operator structurally cannot do — @test\/RASpec.hs@'s
-- @prop_checkDropMatrix@ carries that case directly.
certWrongFractionSites :: Unit -> [(Expected, Constituent, Unit -> Unit)]
certWrongFractionSites u =
  [ ( ExpectClass R13
    , CArgument ix
    , rewriteArg ix (rewriteAt pos (setPayload payload'))
    )
  | (ix, pos, SRule _ _ _ _ _ (AssuranceCert cert)) <- ruleSites u
  , certBackend cert == BackendId "ra"
  , certVersion cert == 1
  , Just payload' <- [bumpWitness (certPayload cert)]
  ]
  where
    setPayload p (SRule r theta ws d hs (AssuranceCert cert)) =
      SRule r theta ws d hs (AssuranceCert cert {certPayload = p})
    setPayload _ t = t

-- | Rewrite a @(radrop SLOT SLOT (frac P Q))@ payload to carry @(P+1)/Q@,
-- renormalized, leaving both premise slots untouched. The witness is the
-- certified value, so bumping it always changes what the certificate claims
-- while @(%)@ keeps the result in lowest terms with a positive denominator and
-- 'show' emits the canonical numerals the decoder demands —
-- 'parseCanonicalInt' for the numerator (where a leading @-@ is canonical),
-- 'parseCanonicalNat' for the denominator, which the @qn <= 0@ guard keeps
-- positive. The mutant therefore stays decodable by construction.
--
-- 'Nothing' when the payload is not that shape, so a site is offered only where
-- the corruption is meaningful. The head keywords are recognized through
-- 'parseTag' and echoed back verbatim rather than respelled here: the concrete
-- spelling stays owned by "Lara.Strict.RA".
bumpWitness :: SExpr -> Maybe SExpr
bumpWitness (SList [SAtom k, slotF, slotA, SList [SAtom kf, SAtom p, SAtom q]])
  | parseTag k == Just TRadrop
  , parseTag kf == Just TFrac = do
      pn <- parseCanonicalInt p
      qn <- parseCanonicalNat q
      if qn <= 0
        then Nothing
        else
          let r = (pn + 1) % qn
           in Just
                ( SList
                    [ SAtom k
                    , slotF
                    , slotA
                    , SList
                        [ SAtom kf
                        , SAtom (show (numerator r))
                        , SAtom (show (denominator r))
                        ]
                    ]
                )
bumpWitness _ = Nothing
