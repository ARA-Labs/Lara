-- | The strict-certificate seam (spec §5; @docs/strict-backend-decision.md@ §2–§3).
--
-- LARA has __one__ claim-support calculus and __one__ small seam for strict
-- certificates. A strict rule instance may carry an opaque certificate checked
-- by a /registered/ backend. The claim-support calculus knows neither the
-- backend's proof-term grammar nor its axioms — it only asks
--
-- > strictCheck(beta, T, [premise conclusions], goal, kappa) = accept | reject
--
-- and receives back @accept@ with a dependency set, or a rejection. A backend's
-- formulas and proof terms are __never__ source constructs; conversely no
-- backend proof term can be reinserted as a source proposition. This is the
-- __factivity firewall__ (decision doc §3): a successful check discharges the
-- /deductive validity/ of this step relative to the premise conclusions and the
-- declared theory; it does __not__ assert that any premise is true.
--
-- == The interface (decision doc §2)
--
-- Each backend fixes its own formula, certificate, and theory types /internally/
-- (see "Lara.Strict.ND"). At this seam every backend speaks the same language:
--
--   * it receives normalized source 'Prop's for the premise conclusions and the
--     goal (it applies its own @encode_beta@ inside);
--   * it receives the certificate as an opaque 'SExpr' wire value that it alone
--     decodes (closed registration — an artifact cannot upload code, axioms, or
--     a new encoding, decision doc §2 obligation 5);
--   * on acceptance it returns exactly the 'Dependency' set it consulted
--     (dependency accountability, obligation 4).
--
-- The @models_beta@ semantics used to /state/ soundness (obligation 3) and the
-- structural consequence laws (obligation 6) are mathematics about a backend's
-- checker, not runtime code; they live in each adapter's soundness theorem and
-- its property suite, not in this module.
--
-- == The LCF seal
--
-- 'StrictJudgment' is __sealed__: its constructor is not exported, so the only
-- way to obtain one is to call 'strictCheck' and have a registered backend
-- accept. A @StrictJudgment@ is therefore a machine-checked certificate that its
-- conclusion was discharged by a registered backend under a named theory — the
-- same discipline as "Lara.Kernel"'s @Judgment@, lifted to the backend seam.
module Lara.Strict
  ( -- * Backend identity and theories
    BackendId (..)
  , TheoryDigest (..)
    -- * Dependencies
  , Dependency (..)
    -- * The opaque certificate wire form
  , SExpr (..)
    -- * Backends and the closed registry
  , Backend (..)
  , Registry
  , mkRegistry
  , lookupBackend
    -- * The sealed strict judgment
  , StrictJudgment
  , sjBackend
  , sjTheory
  , sjConclusion
  , sjDependencies
    -- * Checking a strict step
  , StrictError (..)
  , strictCheck
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)

import Lara.Prop (Prop)

-- ---------------------------------------------------------------------------
-- Identity and theories
-- ---------------------------------------------------------------------------

-- | A registered backend is named by a fixed @(name, version)@ pair. Programs
-- may /select/ a backend by this identifier but may not define one at runtime
-- (decision doc §2 obligation 5).
data BackendId = BackendId
  { backendName    :: String
  , backendVersion :: Int
  }
  deriving (Eq, Ord, Show)

-- | A digest that addresses a finite, versioned background theory. The theory
-- itself is fixed inside the backend; a program selects it by digest and cannot
-- alter its contents (decision doc §2 obligation 5, §3).
newtype TheoryDigest = TheoryDigest String
  deriving (Eq, Ord, Show)

-- ---------------------------------------------------------------------------
-- Dependencies
-- ---------------------------------------------------------------------------

-- | A slot consulted by an accepted certificate (decision doc §2 obligation 4).
-- Locally introduced and discharged assumptions are __not__ dependencies; only
-- free premise slots and theory entries are reported.
data Dependency
  = -- | premise slot @i@ (0-based, in the order premises were supplied)
    PremiseSlot Int
  | -- | entry @i@ (0-based) of the digest-addressed theory
    TheoryEntry Int
  deriving (Eq, Ord, Show)

-- ---------------------------------------------------------------------------
-- The opaque certificate wire form
-- ---------------------------------------------------------------------------

-- | The certificate as it reaches the seam: an opaque S-expression the backend
-- alone decodes. S-expressions (not JSON) are the on-disk differential-testing
-- anchor (exploration-tree N11); at this layer they are constructed as abstract
-- syntax values — a textual reader is a later, separate concern.
data SExpr
  = SAtom String
  | SList [SExpr]
  deriving (Eq, Ord, Show)

-- ---------------------------------------------------------------------------
-- Backends and the closed registry
-- ---------------------------------------------------------------------------

-- | A registered backend, reduced to what the seam needs. Its formula,
-- certificate, and theory types are private to its implementing module; here it
-- exposes a single total, deterministic check (decision doc §2 obligation 1,
-- decidable replay).
--
-- @'runBackend' digest premises goal cert@ resolves @digest@ against the
-- backend's /fixed/ theory table, encodes @premises@ and @goal@ with the
-- backend's own @encode_beta@, decodes @cert@, replays it, and on success
-- returns the exact 'Dependency' set consulted (obligation 4). A @Left@ carries
-- a human-readable rejection reason, including an unknown theory digest.
data Backend = Backend
  { backendId  :: BackendId
  , runBackend :: TheoryDigest -> [Prop] -> Prop -> SExpr -> Either String (Set Dependency)
  }

-- | The fixed backend registry @R@. Closed: it is built once, in code, from a
-- known list of adapters — an artifact cannot add to it.
newtype Registry = Registry (Map BackendId Backend)

-- | Build a registry from a fixed list of backends. A later backend with a
-- duplicate identifier shadows an earlier one.
mkRegistry :: [Backend] -> Registry
mkRegistry bs = Registry (Map.fromList [(backendId b, b) | b <- bs])

-- | Look up a backend by identifier. 'Nothing' means the backend is not
-- registered — a program cannot introduce it.
lookupBackend :: Registry -> BackendId -> Maybe Backend
lookupBackend (Registry m) i = Map.lookup i m

-- ---------------------------------------------------------------------------
-- The sealed strict judgment
-- ---------------------------------------------------------------------------

-- | A checked strict step. The constructor is intentionally hidden: only
-- 'strictCheck' builds one, so a @StrictJudgment@ certifies that a registered
-- backend accepted @sjConclusion@ under @sjTheory@, consulting exactly
-- @sjDependencies@. It exposes /only/ source-visible data — never a backend
-- formula or proof term (the factivity firewall).
data StrictJudgment = StrictJudgment
  { sjBackend      :: BackendId
  , sjTheory       :: TheoryDigest
  , sjConclusion   :: Prop
  , sjDependencies :: Set Dependency
  }
  deriving (Eq, Show)

-- | Why a strict step failed to check.
data StrictError
  = -- | the named backend is not in the registry (decision doc §2 obligation 5)
    UnregisteredBackend BackendId
  | -- | the backend was registered but rejected the step (unknown theory
    -- digest, ill-typed certificate, goal mismatch, …); carries the backend's
    -- reason
    BackendRejected BackendId String
  deriving (Eq, Show)

-- | Check one strict step against the registry. On success the sealed
-- 'StrictJudgment' certifies deductive validity of @goal@ from @premises@ under
-- the backend's declared theory — nothing about the /truth/ of any premise
-- (non-factivity, decision doc §3 / Theorem 3).
strictCheck
  :: Registry
  -> BackendId
  -> TheoryDigest
  -> [Prop]          -- ^ premise conclusions (slot order fixes 'PremiseSlot' indices)
  -> Prop            -- ^ goal (this step's conclusion)
  -> SExpr           -- ^ opaque certificate
  -> Either StrictError StrictJudgment
strictCheck reg bid digest premises goal cert =
  case lookupBackend reg bid of
    Nothing -> Left (UnregisteredBackend bid)
    Just b ->
      case runBackend b digest premises goal cert of
        Left reason -> Left (BackendRejected bid reason)
        Right deps ->
          Right
            StrictJudgment
              { sjBackend = bid
              , sjTheory = digest
              , sjConclusion = goal
              , sjDependencies = deps
              }
