{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ExtendedDefaultRules #-}

module YmlAfa.Afa where

import GHC.Generics (Generic)
import Data.Hashable (Hashable)
import Data.List (intercalate)
import Data.Array (Array)
import Text.InterpolatedString.Perl6 (qq)

data Formula
  = And {_operands :: [Formula]}
  | Or {_operands :: [Formula]}
  | Not Formula
  | Q {_unI :: Int} -- next state
  | A {_unI :: Int} -- input symbol
  | S {_unI :: Int} -- shared gate
  | T
  | F
  deriving (Eq, Generic, Hashable)

instance Show Formula where
  show (And xs) = [qq|(& {intercalate " " $ map show xs})|]
  show (Or xs) = [qq|(| {intercalate " " $ map show xs})|]
  show (Not x) = [qq|(! {show x})|]
  show (Q i) = [qq|q{i}|]
  show (A i) = [qq|a{i}|]
  show (S i) = [qq|s{i}|]
  show T = [qq|t|]
  show F = [qq|f|]

data Afa = Afa
  { _acnt :: Int
  , _sdefs :: Array Int Formula
  , _qdefs :: Array Int Int
  }
  deriving (Generic, Show)

structurallyEqual :: Afa -> Afa -> Bool
(Afa acnt1 sdefs1 qdefs1) `structurallyEqual` (Afa acnt2 sdefs2 qdefs2) =
  acnt1 == acnt2
  && sdefs1 == sdefs2
  && qdefs1 == qdefs2
