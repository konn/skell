{-# LANGUAGE FlexibleInstances, GADTs #-}
module Language.Skell.Parser.S.Untyped where
import           Control.Applicative
import           Data.Attoparsec.ByteString.Char8 ((<?>))
import qualified Data.Attoparsec.ByteString.Char8 as A
import qualified Data.ByteString.Char8            as BS
import           Data.Foldable
import           Data.Fresh
import qualified Data.HashSet                     as HS
import           Language.Skell.Syntax.Untyped
import           Text.Parser.Char
import           Text.Parser.Token
import           Text.Parser.Token.Highlight

parseSkell :: BS.ByteString -> Either String (UExpr Var)
parseSkell = A.parseOnly (A.skipSpace *> skellP' <* A.endOfInput)

keywords :: HS.HashSet String
keywords = HS.fromList
  [ "if", "+", "neg", "*", "abs", "lam"
  , "<", "div", "mod", "pair"
  , "fst", "snd", "=", "is-zero"
  ]

style :: IdentifierStyle A.Parser
style =
  IdentifierStyle
  { _styleName = "Skell-in-S"
  , _styleStart = lower <|> oneOf "&@<>+-=?!:*"
  , _styleLetter = alphaNum <|> oneOf "-_'&@<>+-=?!:*"
  , _styleReserved = keywords
  , _styleHighlight = Identifier
  , _styleReservedHighlight = ReservedIdentifier
  }
{-
skellP' :: A.Parser (UExpr Var)
skellP' = varP
    <|> PrimI . fromIntegral <$> integer
    <|> parens ifteP
    <|> parens appsP
 -}
varP :: A.Parser (UExpr Var)
varP = UVar () <$> ident style <?> "Variable"

ifteP :: A.Parser (UExpr Var)
ifteP = parens $
  UIfte ()
    <$  reserve style "if"
    <*> (skellP' <?> "if-condition")
    <*> (skellP' <?> "then-clasuse")
    <*> (skellP' <?> "else-clause")

fixP :: A.Parser (UExpr Var)
fixP = parens $
  UFix ()
    <$  reserve style "fix"
    <*> (skellP' <?> "fix body")

lamP :: A.Parser (UExpr Var)
lamP = parens $ do
  reserve style "lam"
  v <- brackets $ (ident style <?> "bound variable")
  ULam () . abstract v <$> (skellP' <?> "lambda body")

skellP :: A.Parser (UExpr (UId Var ()))
skellP = cmapBV (fromUV $ error "Unbound variable") . mapFV UV <$> skellP'

skellP' :: A.Parser (UExpr Var)
skellP' = UPrimI () . fromIntegral <$> natural
      <|> A.try (primP <?> "primitive operation")
      <|> A.try (ifteP <?> "ifte expr")
      <|> A.try (fixP <?> "fix expr")
      <|> A.try (lamP <?> "lambda abstraction")
      <|> (appP <?> "application")
      <|> varP

appP :: A.Parser (UExpr Var)
appP = parens $ do
  fun <- skellP'
  args <- skellP' `A.sepBy1` spaces
  return $ foldl (UApp ()) fun args

primP :: A.Parser (UExpr Var)
primP =
      asum
        (map (uncurry primBinP)
        [ ("<", Lt), ("+", Add)
        , ("-", Sub), ("*", Mul)
        , ("div", Div), ("mod", Mod)
        , ("pair", Pair), ("=", Eql)
        ])
  <|> asum (map (uncurry primOpP)
           [("fst", Fst), ("snd", Snd), ("is-zero", IsZero)
           ])

primBinP :: String -> PrimBin -> A.Parser (UExpr Var)
primBinP op bin = parens $
  UPrimBin ()
    <$> (bin <$ reserve style op)
    <*> skellP'
    <*> skellP'

primOpP :: String -> PrimOp -> A.Parser (UExpr Var)
primOpP op f = parens $
  UPrimOp ()
    <$> (f <$ reserve style op)
    <*> skellP'
