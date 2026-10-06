module Lara.Evidence.Internal where

import qualified Data.ByteString as B
import Lara.AST (LeafId)
import Lara.Evidence.Manifest
import Lara.Evidence.Types
import Lara.Prop (Prop)

data CapturedObject = CapturedObject ObjectMeta B.ByteString deriving (Eq,Show)
newtype Snapshot = Snapshot [CapturedObject] deriving (Eq,Show)
data SuccessfulJudgment = SuccessfulJudgment LeafId ExtractionRequest Prop [ObjectMeta] deriving (Eq,Show)
