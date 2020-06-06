{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

module YmlAfa.Elementary where

import Control.Arrow
import Control.Monad.ST
import Control.Monad.State
import Data.Array
import Data.Array.IO
import Data.Array.MArray
import Data.Array.Unsafe
import System.IO.Unsafe

import YmlAfa.Afa

bottom_up :: ((Int -> Int) -> Formula -> State Int [Formula]) -> [Formula] -> [Formula]
bottom_up fn fs = unsafePerformIO$ do
  (arr :: IOUArray Int Int) <- newArray_ (0, length fs - 1)
  arr' <- unsafeFreeze arr

  let
    step :: ([[Formula]], Int, Int) -> Formula -> IO ([[Formula]], Int, Int)
    step (result, i, j) f = do
      let (fs', i') = runState (fn (arr'!) f) i
      writeArray arr j i
      return (fs' : result, i', j + 1)

  concat . reverse . (\(x, _, _) -> x) <$> foldM step ([], 0, 0) fs
