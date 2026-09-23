-- | Term-level strict-certificate dependency accounting (spec §6; the Haskell
-- mirror of @Lara.Support.certDeps@ in @lean\/Lara\/Support.lean@).
--
-- The reported dependency set of a support term is @leaves(w) ∪ certDeps(w)@.
-- "Lara.SupportTerm".@leaves@ is the source-leaf half; this module is the
-- certificate half — the union, over every 'AssuranceCert' node in the term, of
-- that step's backend report, resolved to a typed 'CertDep' and tagged with the
-- backend that produced it. Discharge subterms are walked, so a certificate
-- under a defeasible ancestor is accounted exactly like one on the premise
-- spine.
--
-- == Why this hangs off 'CertOk' and not off a registry
--
-- The collector takes the same oracle the checked graph consults — the one
-- @Lara.Driver.buildCertOk@ builds — so a report can only be collected from a
-- step the shipped checker would itself accept. Building it on
-- 'Lara.Strict.strictCheck' instead would have produced accounting for a code
-- path production never runs: @strictCheck@ is reached only from @test\/@,
-- while the real checker goes through @buildCertOk@. That is also why
-- 'Lara.SupportTerm.CertOutcome' retains the report at all (design note D9,
-- "Lara.SupportTerm") — before it, the production path computed each backend's
-- report and dropped it.
--
-- == Agreement with the mechanization
--
-- On /checked/ terms this agrees with Lean's @certDeps@. The two differ only in
-- totality: Lean's @stepDeps@ resolves a certificate node whenever its rule,
-- premise instantiation, and backend resolve, so it reports a resolvable
-- certificate's uses even when acceptance fails, whereas this collector sees a
-- report only through 'CertAccepted'. On typed terms — the only terms any
-- theorem quantifies over — acceptance holds at every certificate node
-- (Lean @cert_node_accounted@) and the two coincide. A node whose rule or
-- instantiation does not resolve, or whose certificate the oracle rejects,
-- contributes nothing; the walk continues into its subterms regardless, so a
-- rejected step never hides the accounting of the steps beneath it.
--
-- == Design note D7 — where backend identity lives
--
-- Lean's @CertDep.theoryEntry@ carries @BackendId × Digest@; Haskell's
-- 'St.Dependency' carries no identity field at all, because identity lives one
-- level up, in @StrictJudgment.sjBackend@. Widening 'St.Dependency' to carry it
-- would ripple into all three adapters ("Lara.Strict.ND",
-- "Lara.Strict.Ord", "Lara.Strict.RA") for no gain — each already knows
-- which backend it is. Instead this collector tags each step's report with that
-- step's backend as it walks.
--
-- The identity types are pinned deliberately. The AST 'Cert' carries a
-- __name-only__ 'BackendId' with the version in a separate 'certVersion' field,
-- while Lean's @BackendId@ is @(name, version)@. The tag must therefore be
-- 'St.BackendId' (name /and/ version) and 'St.TheoryDigest', built here by the
-- same conversions @buildCertOk@ uses to reach the registry — tagging with the
-- AST types would collide two same-name different-version backends into one
-- indistinguishable report.
--
-- The premise\/theory asymmetry is Lean's, not an oversight: a premise
-- dependency carries no backend identity because it names a source-visible
-- premise slot of its own reporting node, which the reader can already see;
-- a theory dependency names an entry of a digest-addressed table that only the
-- backend can resolve, so it must say which backend and which digest.
--
-- == Where the report surfaces
--
-- Production 'Lara.SupportTerm.inferSupport' still reads only the acceptance
-- projection 'Lara.SupportTerm.certAccepted' — that is design note D9 and it is
-- unchanged: no checked-graph decision may consult dependency data. What
-- changed is that the /report/ now has a shipped consumer. The
-- driver runs this collector over the accepted unit's arguments
-- ("Lara.Driver".'Lara.Driver.unitCertDeps', reached through
-- 'Lara.Driver.runCheckDeps' and the @lara deps@ subcommand), so the
-- accountability result @certDeps@ mechanizes — Lean @cert_steps_accounted@ and
-- @certDeps_eq_union@ — has a production observable.
--
-- __The collector is not re-implemented on that path.__ The driver calls this
-- function, not a fused copy inside 'Lara.SupportTerm.inferSupport'. A fused
-- collector would be a /second/ implementation of the same accounting, owing
-- its own agreement argument against Lean; calling this one means the text a
-- consumer reads is produced by the very mirror that
-- @scripts\/check-backend-deps-golden.sh@ pins against the Lean witness, byte
-- for byte. The cost is that an accepted certificate node is replayed once more
-- when — and only when — a caller demands the report; the oracle is a pure
-- function, so the second application cannot disagree with the first (the same
-- argument 'Lara.SupportTerm.assuranceError' already relies on).
--
-- The verdict is not widened. @lara check@'s @stdout@ is the frozen wire
-- verdict and a differential anchor against the Lean driver
-- (@scripts\/differential.sh@); the report rides on its own subcommand instead,
-- so no anchor, golden, or freeze tag moves. That decision is recorded in
-- @docs\/spec.md@ §6.
module Lara.Strict.Deps
  ( CertDep (..)
  , certDeps
    -- * Canonical rendering (the cross-language golden encoding)
  , encodeCertDep
  , encodeCertDeps
  ) where

import Data.List (nub, sort)
import qualified Data.Set as Set

import Lara.AST
  ( Assurance (..)
  , BackendId (..)
  , Cert (..)
  , Rule (..)
  , RuleId
  , SupportTerm (..)
  , TheoryDigest (..)
  )
import Lara.Prop (FunSym (..), Pred (..), Prop (..), Term (..))
import qualified Lara.Strict as St
import Lara.SupportTerm (CertOk, CertOutcome (..), instAPat, instAPats)

-- | A resolved strict-certificate dependency (Lean @Lara.Support.CertDep@).
--
-- The two constructors are the premise\/theory split 'St.Dependency' already
-- makes; what is added here is resolution and identity. A premise slot is
-- resolved to the instantiated premise atom it names — the reader can then see
-- /what/ was consulted, not merely which position — and a theory entry is
-- tagged with the backend and digest that address the table it indexes (design
-- note D7 above).
data CertDep
  = -- | premise slot @i@ of the reporting node, resolved to that node's
    -- instantiated premise atom (Lean @CertDep.premise@)
    CertPremise Int Prop
  | -- | entry @t@ of the reporting certificate's digest-addressed theory
    -- (Lean @CertDep.theoryEntry@)
    CertTheory St.BackendId St.TheoryDigest Int
  deriving (Eq, Ord, Show)

-- | @certDeps(w)@ (spec §6): every certificate node's report, in the order Lean
-- collects them — this node, then the premise subterms left to right, then the
-- discharge subterms in declaration order.
--
-- @Pi@ is the same rule lookup 'Lara.SupportTerm.inferSupport' takes, and it is
-- needed for the same reason: the oracle is applied to the instantiated premise
-- atoms @As@ and conclusion @C@, which are @instAPats theta (rulePremises r)@
-- and @instAPat theta (ruleConclusion r)@ — exactly what the checker computes
-- before calling @certOk cert as c@. On a checked term those atoms are the
-- premise subterms' conclusions up to @≡@, so this asks the oracle the same
-- question the checker asked.
--
-- Only the /traversal/ order is shared with Lean. Within one node the entries
-- come out in 'St.Dependency' order, because a Haskell adapter reports a 'Set'
-- where Lean's @Backend.uses@ is a list; the two agree as collections, which is
-- what every accountability statement is about, and neither side's per-node
-- sequence is a contract.
certDeps :: CertOk -> (RuleId -> Maybe Rule) -> SupportTerm -> [CertDep]
certDeps certOk pI = go
  where
    go w = case w of
      SLeaf _ -> []
      SRule rn theta ws d _ a ->
        stepDeps rn theta a
          ++ concatMap go ws
          ++ concatMap (go . snd) d

    -- The report of one node, empty for anything that is not an accepted
    -- certificate instance (Lean @stepDeps@).
    stepDeps rn theta a = case a of
      AssuranceCert cert
        | Just r <- pI rn
        , Just as <- instAPats theta (rulePremises r)
        , Just c <- instAPat theta (ruleConclusion r)
        , CertAccepted deps <- certOk cert as c ->
            concatMap (resolve cert as) (Set.toList deps)
      _ -> []

    -- Resolve one reported slot against the reporting node. The premise/theory
    -- split is already made by the adapter, which derives it from the premise
    -- count it was handed (see @toDependency@ in "Lara.Strict.ND"), so a
    -- 'St.PremiseSlot' of a registered backend is always in range of @As@ and
    -- this list is always a singleton. It is a list, not a 'CertDep', so that
    -- the function stays total without inventing an atom: a hypothetical
    -- adapter reporting an out-of-range premise slot contributes nothing rather
    -- than indexing past the end of @As@.
    resolve cert as dep = case dep of
      St.PremiseSlot i
        | i >= 0, atom : _ <- drop i as -> [CertPremise i atom]
        | otherwise -> []
      St.TheoryEntry t -> [CertTheory (backendOf cert) (digestOf cert) t]

    -- The registry-facing identity of the certificate's backend: the AST splits
    -- @(name, version)@ across 'certBackend' and 'certVersion', and these are
    -- the same two conversions @Lara.Driver.buildCertOk@ applies before
    -- 'St.lookupBackend' (design note D7 above).
    backendOf cert = case certBackend cert of
      BackendId name -> St.BackendId name (certVersion cert)

    digestOf cert = case certTheory cert of
      TheoryDigest s -> St.TheoryDigest s

-- ---------------------------------------------------------------------------
-- Canonical rendering (the cross-language golden encoding)
-- ---------------------------------------------------------------------------

-- | Escape and quote one string: backslash, double quote, newline and tab
-- become their two-character escapes; everything else is passed through.
-- Mirrors @quoteGolden@ in the Lean witness.
quoteEnc :: String -> String
quoteEnc s = '"' : concatMap esc s ++ "\""
  where
    esc '\\' = "\\\\"
    esc '"' = "\\\""
    esc '\n' = "\\n"
    esc '\t' = "\\t"
    esc c = [c]

-- | Encode a ground term. Mirrors @encodeTermGolden@ in the Lean witness.
encodeTermEnc :: Term -> String
encodeTermEnc t = case t of
  TNum s -> "(num " ++ quoteEnc s ++ ")"
  TStr s -> "(str " ++ quoteEnc s ++ ")"
  TCon (FunSym k) ts -> "(con " ++ quoteEnc k ++ encodeTermsEnc ts ++ ")"

-- | Encode an argument list, each element preceded by a single space.
encodeTermsEnc :: [Term] -> String
encodeTermsEnc = concatMap ((' ' :) . encodeTermEnc)

-- | Encode a ground proposition. Mirrors @encodeAtomGolden@ in the Lean witness
-- (Lean's @Atom@ is this 'Prop').
encodeAtomEnc :: Prop -> String
encodeAtomEnc (Prop (Pred p) ts) =
  "(atom " ++ quoteEnc p ++ encodeTermsEnc ts ++ ")"

-- | Encode one dependency as its canonical line. The grammar, shared verbatim
-- with @encodeCertDepGolden@ in @lean\/Lara\/Examples\/BackendComposition.lean@:
--
-- @
--   line   ::= "premise " nat " " atom
--            | "theory " qstr " " nat " " qstr " " nat
--   atom   ::= "(atom " qstr terms ")"
--   terms  ::= { " " term }
--   term   ::= "(num " qstr ")" | "(str " qstr ")" | "(con " qstr terms ")"
--   qstr   ::= '"' { char | "\\\\" | "\\\"" | "\\n" | "\\t" } '"'
-- @
--
-- The @theory@ line's two naturals are the backend /version/ and the theory
-- /entry index/; its two quoted strings are the backend name and the theory
-- digest. __Nothing is dropped__: every field of both 'CertDep' constructors is
-- encoded, including the premise slot's resolved atom in full ground form. The
-- premise\/theory asymmetry is 'CertDep''s own (design note D7 above) — a
-- premise dependency genuinely carries no backend identity — not an omission
-- made to force the two languages to agree.
--
-- This encoding was the @test\/StrictSpec.hs@ golden encoder. It is
-- in the library now because the shipped @lara deps@ report and the
-- cross-language golden must be the /same/ text: a report format defined
-- separately from the one @scripts\/check-backend-deps-golden.sh@ diffs against
-- Lean would be a format nothing pins.
encodeCertDep :: CertDep -> String
encodeCertDep d = case d of
  CertPremise i atom -> "premise " ++ show i ++ " " ++ encodeAtomEnc atom
  CertTheory (St.BackendId name version) (St.TheoryDigest digest) t ->
    "theory "
      ++ quoteEnc name
      ++ " "
      ++ show version
      ++ " "
      ++ quoteEnc digest
      ++ " "
      ++ show t

-- | The canonical encoding of a whole dependency collection.
--
-- __Sort order.__ Lines are emitted __sorted ascending by the encoded line
-- text__, compared as a sequence of Unicode code points ('Data.List.sort' on
-- 'String', which is exactly the @charListLtGolden@ order the Lean encoder
-- spells out), and __deduplicated__. The order is on the /text/, not on the
-- slot number: slot @10@ sorts before slot @2@. That is deliberate — the order
-- is a canonicalization device, not a semantic ranking.
--
-- __Why deduplicated.__ Lean's per-node report is a @List Nat@
-- (@Backend.uses@); a Haskell adapter reports a 'Data.Set.Set'
-- 'Lara.Strict.Dependency'. A certificate naming the same slot twice —
-- @(ordcmp (prem 0) (prem 0))@ — is a two-element list in Lean and a
-- one-element set here. The two languages agree as /collections/, which is what
-- every accountability statement is about, so multiplicity is deliberately
-- outside this contract and both encoders canonicalize it away.
--
-- The result ends in a newline so it compares equal to the committed golden as
-- read, and to @IO.println@'s output on the Lean side. An empty collection
-- encodes to the empty string, not to a blank line.
encodeCertDeps :: [CertDep] -> String
encodeCertDeps = unlines . sort . nub . map encodeCertDep
