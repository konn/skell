{-# LANGUAGE DeriveAnyClass, DeriveDataTypeable, TypeApplications #-}
module Main where
import           Control.Exception
import           Data.Bifunctor
import qualified Data.ByteString                 as BS
import           Data.Either
import           Data.Fresh
import           Data.Typeable
import           Language.Skell.Eval
import           Language.Skell.Parser.S.Untyped
import           Language.Skell.Syntax.Convert
import           Language.Skell.Syntax.Untyped   (InferenceError (..), infer)
import           Numeric.Natural
import           System.Environment

data CompileError =
    ParseError String
  | InferenceError (InferenceError Var)
  deriving (Show, Eq, Ord, Typeable, Exception)

main :: IO ()
main = do
  args <- getArgs
  src <- case args of
    []       -> BS.getContents
    prog : _ -> BS.readFile prog
  case first InferenceError . infer
       =<< first ParseError (parseSkell src) of
    Right e  -> print e
    Left err -> throw err
