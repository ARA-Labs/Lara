module Lara.BindingAudit.Types
  ( AuditSubjectId (..)
  , AuditSubjectType (..)
  , AuditSubject (..)
  ) where

import Lara.AST (SourceRef)

newtype AuditSubjectId = AuditSubjectId String
  deriving (Eq, Ord, Show)

data AuditSubjectType
  = AuditStrictStep
  | AuditTypedAttack
  deriving (Eq, Ord, Show)

data AuditSubject = AuditSubject
  { auditSubjectId :: AuditSubjectId
  , auditSubjectType :: AuditSubjectType
  , auditSubjectFormalObject :: String
  , auditSubjectProseContext :: String
  , auditSubjectRefs :: [SourceRef]
  }
  deriving (Eq, Show)
