{-# LANGUAGE TypeApplications #-}
module Main where
import qualified Data.ByteString         as BS
import           Language.Skell.Eval
import           Language.Skell.Parser.S
import           Numeric.Natural
import           System.Environment

main :: IO ()
main = do
  args <- getArgs
  src <- case args of
    []       -> BS.getContents
    prog : _ -> BS.readFile prog
  case eval mempty =<< parseSkell @Natural src of
    Right e  -> print e
    Left err -> error err


