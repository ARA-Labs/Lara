-- | Safe public observations and validated policy-table operations for source
-- admission, plus the three deterministic pipeline steps the admission
-- differential (scripts/check-admission.hs) must exercise through the
-- production implementation.  Audit and rejection constructors, and every
-- other minting helper, live in the package-internal
-- "Lara.Admission.Internal" module.
module Lara.Admission
  ( AdmissionCause (..)
  , AdmissionAudit
  , admissionAuditLeaves
  , admissionAuditArgs
  , admissionAuditAttacks
  , admissionAuditIsEmpty
  , AdmissionRejection
  , admissionRejectionLeaf
  , admissionRejectionKind
  , admissionRejectionProvenance
  , admissionRejectionMatchedRow
  , decisionFor
  , validateAdmissionKeys
  , firstAdmissionRejection
  , policyQuarantineSeed
  , buildAdmissionAudit
  , renderAdmissionRejection
  , renderAdmissionAudit
  ) where

import Lara.Admission.Internal
  ( AdmissionAudit
  , AdmissionCause (..)
  , AdmissionRejection
  , admissionAuditArgs
  , admissionAuditAttacks
  , admissionAuditIsEmpty
  , admissionAuditLeaves
  , admissionRejectionKind
  , admissionRejectionLeaf
  , admissionRejectionMatchedRow
  , admissionRejectionProvenance
  , buildAdmissionAudit
  , decisionFor
  , firstAdmissionRejection
  , policyQuarantineSeed
  , renderAdmissionAudit
  , renderAdmissionRejection
  , validateAdmissionKeys
  )
