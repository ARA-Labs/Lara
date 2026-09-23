-- | The reusable @.lara@ source-loading seam: text on disk to a
-- 'PreparedSource', with the parsed 'Program' and 'Policy' kept beside it.
--
-- == Position in the pipeline
--
-- "Lara.Elaborate" is deliberately pure — it does no IO, no parsing, and no
-- filesystem access, and its caller hands it already-parsed values. The four
-- steps between a path and a 'PreparedSource' — read the program, parse it,
-- resolve its co-located policy file, parse that — therefore have to live
-- somewhere outside it, and until now the copy the /product/ used lived inside
-- @app\/Main.hs@, unavailable to anything else.
--
-- It was never the only copy. Five harness scripts spell the same four steps
-- for themselves — @scripts\/infer-sigma.hs@,
-- @scripts\/gen-corpus-units.hs@, @scripts\/gen-worked-examples.hs@,
-- @scripts\/check-corpus-unit.hs@ and @scripts\/surface-conformance.hs@ — and
-- they still do. That is a smaller problem than it looks, because a harness
-- that resolved a policy differently would produce a visibly wrong corpus
-- rather than a silently wrong verdict, but it does mean this module is the
-- seam for the two doors that decide, not for every reader of a @.lara@ file.
--
-- The multi-artifact map ("Lara.Map.Load") needs exactly those four steps, once
-- per member, and it must get __the same answers the CLI would give__: a map
-- that accepted a member the solo door rejects, or vice versa, would make a
-- composite verdict a statement about a different artifact than the one
-- @lara check@ describes. So the steps move here unchanged and both callers go
-- through this module. @app\/Main.hs@ keeps only what is genuinely CLI-shaped:
-- the @lara: @ prefix, the @stderr@ channel, and the exit code.
--
-- == Why the error is a closed sum, and unprefixed
--
-- 'SourceLoadError' is a five-constructor sum, not a rendered 'String', because
-- its two callers need to /classify/ the failure, not merely print it: the map
-- separates a file it could not read (which is the map's own boundary error)
-- from a file it read and could not understand (which is the member's own
-- source boundary), and those are different diagnostics with different
-- attribution. 'renderSourceLoadError' is the single spelling table, and it
-- carries __no @lara: @ prefix__ — the prefix belongs to the CLI that prints to
-- @stderr@, not to the seam. @app\/Main.hs@ prepends it, so the solo door's
-- bytes are exactly what they were before this module existed.
--
-- == Why reads go through a cache
--
-- A map may name one file twice (two members in one directory share a policy
-- file; the manifest's policy file may also be a member's policy file). Reading
-- it once per reference would let one invocation see two different versions of
-- one file if it changed underneath — and a map is defined as a recheck of the
-- members' /current/ bytes, singular. 'SourceCache' is created per invocation
-- and keyed by 'canonicalPathKey', so two spellings that name one file share
-- one entry and every parse works from that retained buffer.
--
-- The precise guarantee, which is narrower than \"exactly once\": within one
-- invocation a file is read at most once __per distinct cache key__, and two
-- spellings share a key whenever 'canonicalPathKey' can canonicalize both. When
-- it cannot — it falls back to the spelled path, see its own note — two
-- spellings of one file get two keys and the file is read twice. That costs
-- correctness nothing here, because the fallback only triggers where the path
-- does not resolve and both reads then report the same failure.
--
-- It is deliberately __not__ a cross-invocation cache: nothing here consults an
-- mtime, a size, or a digest, so a fresh run always rereads, and an edit that
-- leaves the mtime untouched is still seen. 'loadSource' makes a private cache
-- for its one call, which is why the solo door's behaviour is unchanged.
--
-- __Single-threaded by contract.__ A 'SourceCache' is meant to be threaded
-- through one sequential invocation. The lookup-then-insert sequence in
-- 'readCachedFile' is not atomic across its two steps, so concurrent use could
-- read one file twice and keep whichever result landed second; the individual
-- 'Data.IORef.atomicModifyIORef'' does not make the pair safe and is not there
-- to suggest it does. Nothing in this package shares a cache across threads.
module Lara.Source.Load
  ( -- * Loading one source artifact
    LoadedSource
  , loadedProgram
  , loadedPolicy
  , loadedPrepared
  , loadSource
  , loadSourceWith
  , loadPolicyWith
    -- * Per-invocation read cache
  , SourceCache
  , newSourceCache
  , readCachedFile
  , canonicalPathKey
    -- * Boundary failures
  , SourceLoadError (..)
  , renderSourceLoadError
    -- * Co-located policy resolution
  , resolvePolicyPath
  ) where

import Control.Exception (IOException, evaluate, try)
import Data.IORef (IORef, atomicModifyIORef', newIORef, readIORef)
import qualified Data.Map.Strict as Map
import System.Directory (canonicalizePath)
import System.FilePath (takeDirectory, (<.>), (</>))

import Lara.AST (Policy, PolicyId (..), Program, programPolicy)
import Lara.Elaborate
  ( PreparedSource
  , SourceInvalid
  , prepareSource
  , renderSourceInvalid
  )
import qualified Lara.Syntax as Syntax

-- ---------------------------------------------------------------------------
-- Boundary failures
-- ---------------------------------------------------------------------------

-- | Every way the four steps between a path and a 'PreparedSource' can fail.
--
-- The order of the constructors is the order the steps run in, which is also
-- the precedence the solo driver has always had: an unreadable program is
-- reported before a parse error, and a parse error before an elaboration
-- failure. Each is an exit-@2@ decode\/boundary failure for the CLI; the map
-- splits them, and the split is __who chose the path__ rather than which
-- constructor fired.
--
-- On the member path ('Lara.Map.Load.readMemberSource') only 'SourceUnreadable'
-- is the map's own boundary, because the /artifact/ path came from the manifest
-- and the loader resolved it. 'PolicyUnreadable' is the __member's__: that path
-- comes from the member's own @policy@ declaration, so it becomes
-- 'Lara.Map.Types.MBMemberSource' under the member's alias, alongside the two
-- parse errors and the elaboration failure.
--
-- On the manifest's own contract policy
-- ('Lara.Map.Load.readContractPolicy') the roles swap, and for the same reason:
-- there the policy path came from the manifest, so 'PolicyUnreadable' /is/ the
-- map's boundary. Neither constructor is inherently one side or the other.
data SourceLoadError
  = -- | the artifact file could not be read (the path, then the IO failure)
    SourceUnreadable FilePath IOException
  | -- | the artifact file did not parse (the path, then the located reason)
    SourceParseError FilePath Syntax.ParseError
  | -- | the co-located policy file could not be read
    PolicyUnreadable FilePath IOException
  | -- | the co-located policy file did not parse
    PolicyParseError FilePath Syntax.ParseError
  | -- | the program and policy parsed but do not form a valid source
    SourceInvalidError SourceInvalid

-- | One line naming the step that failed and, where the step has one, the file
-- it failed on.
--
-- __No @lara: @ prefix.__ The prefix is the CLI's, and @app\/Main.hs@ prepends
-- it; keeping it out of here is what lets the map embed the same text inside
-- its own member-attributed line without a second tool name appearing in the
-- middle of it.
renderSourceLoadError :: SourceLoadError -> String
renderSourceLoadError err = case err of
  SourceUnreadable path reason -> "cannot read " ++ path ++ ": " ++ show reason
  SourceParseError path parseError -> locatedParseError path parseError
  PolicyUnreadable path reason -> "cannot read policy " ++ path ++ ": " ++ show reason
  PolicyParseError path parseError -> locatedParseError path parseError
  SourceInvalidError invalid -> "source invalid: " ++ renderSourceInvalid invalid

-- | Render a "Lara.Syntax".'Syntax.ParseError' as one located line.
locatedParseError :: FilePath -> Syntax.ParseError -> String
locatedParseError path parseError =
  "parse error at "
    ++ path
    ++ ":"
    ++ show (Syntax.peLine parseError)
    ++ ":"
    ++ show (Syntax.peCol parseError)
    ++ ": "
    ++ Syntax.peReason parseError

-- ---------------------------------------------------------------------------
-- Per-invocation read cache
-- ---------------------------------------------------------------------------

-- | The buffers one invocation has already read, keyed by canonical path.
--
-- __Opaque, and per invocation.__ There is no way to construct one that
-- outlives a run and no way to seed it, so this can never become a build
-- cache: it exists only so that one run reads one file once. The key is
-- 'canonicalizePath''s answer, so two spellings of one file — a relative and an
-- absolute path, or a symlink and its target — share the entry.
newtype SourceCache = SourceCache (IORef (Map.Map FilePath (Either IOException String)))

-- | A fresh, empty cache. Make one per invocation and thread it through every
-- read that invocation performs.
newSourceCache :: IO SourceCache
newSourceCache = SourceCache <$> newIORef Map.empty

-- | Read a file through the cache, forcing the read so an IO failure is caught
-- here rather than escaping from a later thunk.
--
-- The IO failure is cached alongside a success: a path that could not be read
-- once must not be retried within the invocation, or two references to one
-- missing file could disagree about whether it exists.
--
-- Not safe for concurrent use — see the module header. The lookup and the
-- insert are two steps, and nothing serialises them.
readCachedFile :: SourceCache -> FilePath -> IO (Either IOException String)
readCachedFile (SourceCache ref) path = do
  key <- canonicalPathKey path
  cached <- Map.lookup key <$> readIORef ref
  case cached of
    Just result -> pure result
    Nothing -> do
      result <- readFileEither path
      atomicModifyIORef' ref (\table -> (Map.insert key result table, ()))
      pure result

-- | The identity of a file for this module: the canonical path when the
-- filesystem can produce one, and the path as given otherwise.
--
-- Exported because the map loader needs /the same/ notion of "one file" that
-- the cache uses: it rejects two member aliases that name one file, and if its
-- test for sameness disagreed with the cache's, a map could reject a duplicate
-- it then read twice, or read once a pair it had declared distinct. Sharing one
-- function makes the two agree by construction rather than by review.
--
-- 'canonicalizePath' does not require the file to exist — it normalises as far
-- as the path does resolve, which is what lets a missing member still be
-- compared for duplication — but it can still fail (a permission error on a
-- parent directory, for instance). Falling back to the spelled path keeps this
-- total: the worst case is that two spellings of one unreachable file get two
-- identities, and both then report the same failure anyway.
canonicalPathKey :: FilePath -> IO FilePath
canonicalPathKey path =
  either (\e -> const path (e :: IOException)) id <$> try (canonicalizePath path)

-- | Read a file, forcing the read inside 'try' so an IO failure is caught here.
readFileEither :: FilePath -> IO (Either IOException String)
readFileEither file = try $ do
  contents <- readFile file
  _ <- evaluate (length contents)
  pure contents

-- ---------------------------------------------------------------------------
-- Loading one source artifact
-- ---------------------------------------------------------------------------

-- | One @.lara@ artifact, loaded: the parsed presentation 'Program', the parsed
-- 'Policy' it resolved to, and the 'PreparedSource' the two produced.
--
-- __Opaque.__ The three travel together because they are one decision: the
-- 'PreparedSource' was built from /these/ two parsed values, so a caller
-- comparing the policy structure (the map's @CFPolicyStructure@) is comparing
-- the policy that actually produced the elaborated unit beside it. Exporting a
-- constructor would let a caller pair a policy with a source it did not
-- prepare, which is exactly the forgery "Lara.Elaborate" hides its own
-- constructors to prevent.
data LoadedSource = LoadedSource Program Policy PreparedSource

-- | The parsed presentation program. Its declaration order is the authoritative
-- order for anything keyed by what the author wrote — claim names above all,
-- which a 'Lara.AST.Unit' has lost by the time it reaches the checker.
loadedProgram :: LoadedSource -> Program
loadedProgram (LoadedSource program _ _) = program

-- | The parsed policy the program resolved to. Comparing /parsed/ policies is
-- how a caller accepts two files that differ only in comments and whitespace
-- while rejecting a redefinition hiding under a shared policy id.
loadedPolicy :: LoadedSource -> Policy
loadedPolicy (LoadedSource _ policy _) = policy

-- | The prepared source: either the policy's admission decision stopped it, or
-- it is ready for 'Lara.Elaborate.runSourceCheck'.
loadedPrepared :: LoadedSource -> PreparedSource
loadedPrepared (LoadedSource _ _ prepared) = prepared

-- | Load one @.lara@ artifact with a private, single-use cache.
--
-- This is the solo door's entry point: one invocation, one artifact, so the
-- cache has nothing to share and exists only to keep the two code paths
-- identical.
loadSource :: FilePath -> IO (Either SourceLoadError LoadedSource)
loadSource file = do
  cache <- newSourceCache
  loadSourceWith cache file

-- | Load one @.lara@ artifact through a caller-owned cache: read the program,
-- parse it, resolve and read its co-located policy, parse that, and prepare the
-- source. The first failure wins, in that order.
loadSourceWith :: SourceCache -> FilePath -> IO (Either SourceLoadError LoadedSource)
loadSourceWith cache file = do
  programTextOrError <- readCachedFile cache file
  case programTextOrError of
    Left reason -> pure (Left (SourceUnreadable file reason))
    Right programText ->
      case Syntax.parseProgram programText of
        Left parseError -> pure (Left (SourceParseError file parseError))
        Right program -> do
          let policyPath = resolvePolicyPath file (programPolicy program)
          policyOrError <- loadPolicyWith cache policyPath
          pure $ do
            policy <- policyOrError
            case prepareSource program policy of
              Left invalid -> Left (SourceInvalidError invalid)
              Right prepared -> Right (LoadedSource program policy prepared)

-- | Read and parse one policy file through the cache.
--
-- Split out because a map needs it on its own: the manifest names the policy
-- every member is compared against, and that file has no program beside it.
-- Both failures are reported with the @policy@ wording, so a caller can tell
-- a missing policy from a missing artifact without inspecting paths.
loadPolicyWith :: SourceCache -> FilePath -> IO (Either SourceLoadError Policy)
loadPolicyWith cache path = do
  policyTextOrError <- readCachedFile cache path
  pure $ case policyTextOrError of
    Left reason -> Left (PolicyUnreadable path reason)
    Right policyText -> case Syntax.parsePolicy policyText of
      Left parseError -> Left (PolicyParseError path parseError)
      Right policy -> Right policy

-- | Co-located policy resolution (D-Arch-2): read @\<policyId\>.policy.lara@
-- from the /same directory/ as the artifact. E.g. @examples\/A\/example.lara@
-- declaring @policy empirical-v1@ resolves to
-- @examples\/A\/empirical-v1.policy.lara@.
--
-- The rule is relative to the __artifact__, never to the process working
-- directory, which is what lets a map resolve a member's policy correctly no
-- matter where the map was run from.
resolvePolicyPath :: FilePath -> PolicyId -> FilePath
resolvePolicyPath artifact (PolicyId pid) =
  takeDirectory artifact </> pid <.> "policy" <.> "lara"
