-- | Public whole-unit checker API.  The source-boundary operation that pairs a
-- raw 'Lara.Replay.CheckInput' with a 'Lara.Blocked.Prune' is intentionally
-- package-internal; source callers can only obtain that pairing through
-- 'Lara.Elaborate.prepareSource'.
module Lara.Driver
  ( buildGamma
  , quarantinedLeaves
  , groupConsistent
  , supportUsesLeaf
  , quarantineUnit
  , Prune
  , prune
  , pruneWithPolicySeed
  , pruneDeclared
  , pruneChecked
  , groupConflictReject
  , groupConflictMessage
  , rejectionDiagnostics
  , buildCertOk
  , buildAccept
  , runCheck
  , runCheckLocated
  , runCheckLocatedWith
  ) where

import Lara.Driver.Internal
  ( Prune
  , buildAccept
  , buildCertOk
  , buildGamma
  , groupConflictMessage
  , groupConflictReject
  , groupConsistent
  , prune
  , pruneChecked
  , pruneDeclared
  , pruneWithPolicySeed
  , quarantineUnit
  , quarantinedLeaves
  , rejectionDiagnostics
  , runCheck
  , runCheckLocated
  , runCheckLocatedWith
  , supportUsesLeaf
  )
