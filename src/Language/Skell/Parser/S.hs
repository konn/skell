{-# LANGUAGE FlexibleInstances, GADTs #-}
module Language.Skell.Parser.S where
import           Control.Applicative
import qualified Data.Attoparsec.ByteString.Char8 as A
import qualified Data.ByteString.Char8            as BS
import           Data.Foldable
import           Data.Fresh
import qualified Data.HashSet                     as HS
import           Data.Type.Equality
import           Language.Skell.Syntax
import           Numeric.Natural
import           Text.Parser.Char
import           Text.Parser.Token
import           Text.Parser.Token.Highlight

class ParseSkell a where
  skellP :: A.Parser (Expr a (Id Var))

parseSkell :: ParseSkell a => BS.ByteString -> Either String (Expr a (Id Var))
parseSkell = A.parseOnly (A.skipSpace *> skellP <* A.endOfInput)

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
skellP :: A.Parser (Expr Natural (Id Var))
skellP = varP
    <|> PrimI . fromIntegral <$> integer
    <|> parens ifteP
    <|> parens appsP
 -}
varP :: HasTypeRep a => A.Parser (Expr a (Id Var))
varP = Var . V <$> ident style

ifteP :: ParseSkell a => A.Parser (Expr a (Id Var))
ifteP = parens $
  Ifte <$  reserve style "if"
       <*> skellP
       <*> skellP
       <*> skellP

fixP :: (HasTypeRep a, ParseSkell a) => A.Parser (Expr a (Id Var))
fixP = parens $
  Fix <$  reserve style "fix"
      <*> skellP

lamP :: (HasTypeRep a, ParseSkell b) => A.Parser (Expr (a -> b) (Id Var))
lamP = parens $ do
  reserve style "lam"
  v <- brackets $ ident style
  either (error . show) Lam . abstract v <$> skellP

instance ParseSkell Natural where
  skellP = PrimI . fromIntegral <$> natural
       <|> A.try primP <|> A.try ifteP <|> A.try fixP <|> varP

instance (HasTypeRep a, HasTypeRep b, ParseSkell b)
      => ParseSkell (a -> b) where
  skellP = A.try lamP <|> A.try ifteP <|> A.try fixP <|> varP

primP :: A.Parser (Expr Natural (Id Var))
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

primBinP :: String -> PrimBin -> A.Parser (ExprF Natural (Id Var) (Id Var))
primBinP op bin = parens $
  PrimBin <$> (bin <$ reserve style op)
          <*> skellP
          <*> skellP

primOpP :: String -> PrimOp -> A.Parser (ExprF Natural (Id Var) (Id Var))
primOpP op f = parens $
  PrimOp <$> (f <$ reserve style op)
         <*> skellP
