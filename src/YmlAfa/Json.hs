{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module YmlAfa.Json where

import Data.Array (listArray, elems)
import Data.Aeson (FromJSON, parseJSON, withObject, (.:), ToJSON, toJSON, object, (.=))
import Text.Parsec (Parsec, runParser, digit, many1, (<|>), char, between)
import Data.Char (isSpace)

import YmlAfa.Afa (Afa(Afa), Formula(..))

instance FromJSON Afa where
  parseJSON = withObject "Afa"$ \obj -> Afa
    <$> obj .: "acnt"
    <*> do
      strs <- obj .: "sdefs" 
      return$ listArray (0, length strs - 1)$ map parseExpr strs
    <*> do
      qs <- obj .: "qdefs"
      return$ listArray (0, length qs - 1) qs

instance ToJSON Afa where
  toJSON (Afa acnt sdefs qdefs) = object
    [ "acnt" .= acnt
    , "sdefs" .= map show (elems sdefs)
    , "qdefs" .= elems qdefs
    ]

type ExprParser a = Parsec String () a

parseExpr :: String -> Formula
parseExpr str = f
  where Right f = runParser term () ""$ filter (not . isSpace) str

operator :: ExprParser Formula
operator =
  (And <$> (char '&' *> many1 term))
  <|> (Or  <$> (char '|' *> many1 term))
  <|> (Not <$> (char '!' *> term))

term :: ExprParser Formula
term =
  between (char '(') (char ')') operator
  <|> (Q <$> var 'q')
  <|> (A <$> var 'a')
  <|> (S <$> var 's')
  <|> (const T <$> char 't')
  <|> (const F <$> char 'f')

var :: Char -> ExprParser Int
var vtype = read <$> (char vtype *> many1 digit)
