-- P8 authoring helper: use the sanctioned impact API solely to produce syntax.
-- Semantic expectations remain in the independently reviewed Python tables.
module Main where
import qualified Data.ByteString as BS
import System.Environment (getArgs)
import System.Exit (die)
import Lara.Prop (Prop(..), Pred(..))
import qualified Lara.Process.Inquiry.Wire as W
import qualified Lara.Process.Inquiry.Types as Q
import qualified Lara.Process.Impact as I
import qualified Lara.Process.ResultWire as R
import qualified Lara.Wire as Raw
main :: IO ()
main = do
  args <- getArgs
  case args of
    [path] -> do
      bytes <- BS.readFile path
      input <- either (die . show) pure (W.parseInquiryInputBS bytes)
      case Q.inquiryRequests input of
        [Q.ImpactRequest _ before after _] ->
          putStrLn (Raw.printSExpr (R.encodeImpactCertificate
            (I.impactCertificate (I.compareEndpoints (I.observeEndpoint before) (I.observeEndpoint after) [Prop (Pred "t") []]))))
        _ -> die "expected exactly one impact request"
    _ -> die "usage: inquiry-impact-producer INPUT"
