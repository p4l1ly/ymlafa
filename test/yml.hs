module Main where

import Data.Either
import Data.Array
import Control.Monad
import Data.Yaml (decodeThrow, encode)
import System.Exit (exitFailure)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as B8

import YmlAfa.Afa
import YmlAfa.Json
import Paths_ymlafa

afa :: Afa
afa = Afa
  { _acnt = 1
  , _sdefs = listArray (0, 1) [T, And [A 0, Q 1]]
  , _qdefs = listArray (0, 1) [1, 0]
  }

main = do
    datadir <- getDataDir

    yml <- B.readFile$ datadir ++ "/afa-examples/a.yml"
    parsed_afa <- decodeThrow yml

    when (not$ parsed_afa `structurallyEqual` afa)
      exitFailure

    let yml' = encode afa
    B8.putStrLn yml'
    parsed_afa' <- decodeThrow yml'
    when (not$ parsed_afa' `structurallyEqual` afa)
      exitFailure
