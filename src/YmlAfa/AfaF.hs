{-# LANGUAGE DeriveFunctor, DeriveTraversable, DeriveFoldable, FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DerivingStrategies, DerivingVia #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}

module YmlAfa.AfaF where

import Debug.Trace

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as M

import GHC.Generics
import Control.Monad
import Control.Monad.Identity
import Control.Monad.ST
import Control.Monad.Reader
import Control.Monad.State.Lazy
import Data.Bifunctor
import Data.Bitraversable
import Data.Either
import Data.Function.Apply
import Data.Functor.Foldable
import qualified Data.Functor.Foldable as RS
import Data.Functor.Compose
import Data.Foldable
import Data.Hashable
import Data.Functor.Classes
import Data.Array.IArray
import Data.Array.ST

import Generic.Data (gliftEq, gshowsPrec, gliftShowsPrec)
import Data.Hashable.Lifted
import Generic.Data.Orphans


type TreeGraphF f ref = Compose (Either ref) f
type TreeGraph f ref = Fix (TreeGraphF f ref)

toTree
  :: Functor f
  => (ref -> TreeGraph f ref)
  -> TreeGraph f ref
  -> Fix f
toTree fromRef = cata$ \case
  Compose (Left ref) -> toTree fromRef$ fromRef ref
  Compose (Right x) -> Fix x

treeDag_cataM_unsorted
  :: forall f m ref a. (Traversable f, Monad m)
  => (ref -> (TreeGraph f ref, m (Maybe a), a -> m ()))
  -> (f a -> m a)
  -> TreeGraph f ref
  -> m a
treeDag_cataM_unsorted fromRef algebra = helper where
  helper :: TreeGraph f ref -> m a
  helper (Fix (Compose (Left ref))) =
    let (child, read, write) = fromRef ref in do
      val <- read
      case val of
        Just val -> return val
        Nothing -> do
          result <- helper child
          write result
          return result
  helper (Fix (Compose (Right x))) = do
    x' <- traverse helper x
    algebra x'

treeDag_cata
  :: (Functor f, Ix ix, Ix ix, IArray arr a, Functor (arr ix))
  => (f a -> a)
  -> [TreeGraph f ix]
  -> (ix, ix)
  -> arr ix a
treeDag_cata alg xs bounds = result where
  result = listArray bounds$ flip map xs$ cata$ \case
    Compose (Left ref) -> result ! ref
    Compose (Right x) -> alg x

separateTerminals :: (Functor f, Foldable f) => f b -> Either (f b) (f a)
separateTerminals node
  | null (toList node) = Right (fmap undefined node)
  | otherwise = Left node

withFst :: (Applicative f, Bitraversable t) => (a -> f c) -> t a b -> f (t c b)
withFst action = bisequence . bimap action pure

type RefOrTerminal f a = Either Int (f a)

collect :: (Monad m) => a -> StateT (Int, [a]) m Int
collect a = do
  i <- state$ \(i, as) -> (i, (i + 1, a : as))
  return i

data HashState a = HashState
  { next_ix :: Int
  , struct_list :: [a]
  , struct_hash :: HashMap a Int
  }
  deriving Show

hashState_empty = HashState 0 [] M.empty

hashCons :: (Eq a, Hashable a, Monad m) => a -> StateT (HashState a) m Int
hashCons a = do
  HashState next_ix struct_list struct_hash <- get

  let ((result, mod), hash) = M.alterF-$ a-$ struct_hash$ \case
        old@(Just ix) -> ((ix, HashState next_ix struct_list), old)
        _ -> ((next_ix, HashState (next_ix + 1) (a : struct_list)), Just next_ix)

  put$ mod hash
  return result

type RefArr s a = STArray s Int a

connect
  :: (MonadTrans t, Monad (t (ST s)))
  => RefArr s a
  -> [RefArr s a -> (t (ST s)) a]
  -> (t (ST s)) [a]
connect arr actions =
  forM (zip [0..] actions)$ \(i, action) -> do
    x <- action arr
    lift$ writeArray arr i x
    return x

connectWithArr
  :: (MonadTrans t, Monad (t (ST s)))
  => [RefArr s a -> (t (ST s)) a]
  -> t (ST s) [a]
connectWithArr actions = do
  arr <- lift$ newArray_ (0, length actions - 1)
  connect arr actions

treeDag_cataM
  :: forall f t s ref a. (Traversable f, MonadTrans t, Monad (t (ST s)), Ix ref)
  => STArray s ref a
  -> (f a -> t (ST s) a)
  -> TreeGraph f ref
  -> t (ST s) a
treeDag_cataM arr alg = helper where
  helper (Fix (Compose (Left ref))) = lift$ readArray arr ref
  helper (Fix (Compose (Right tree))) = traverse helper tree >>= alg

cataM :: (Monad m, Traversable (Base t), Recursive t)
  => (Base t a -> m a) -> t -> m a
cataM alg = c where
  c = alg <=< traverse c . project

-- examples ----------------------------------------------------------------------------

broken_consed ::
  ( [Either Int (SumExprF ())]
  , [SumExprF (Either Int (SumExprF ()))]
  )
broken_consed
  = second struct_list
  $ runST
  $ flip runStateT hashState_empty
  $ connectWithArr
  $ flip map [sumExpr_graph_fromRef 0, sumExpr_graph]
  $ \g arr -> treeDag_cataM arr (withFst hashCons . separateTerminals) g

broken ::
  ( [Either Int (SumExprF ())]
  , [SumExprF (Either Int (SumExprF ()))]
  )
broken
  = second snd
  $ runST
  $ flip runStateT (0, [])
  $ connectWithArr
  $ flip map [sumExpr_graph_fromRef 0, sumExpr_graph]
  $ \g arr -> treeDag_cataM arr (withFst collect . separateTerminals) g


data FormulaF rec
  = And [rec]
  | Or [rec]
  | Not rec
  | Q Int
  | A Int
  | T
  | F
  deriving
    (Functor, Foldable, Traversable, Show, Eq, Generic, Hashable, Generic1, Hashable1)

type Formula = Fix FormulaF

data SumExprF rec
  = Val Int
  | Plus rec rec
  deriving
    (Functor, Foldable, Traversable, Show, Eq, Generic, Hashable, Generic1, Hashable1)

instance Eq1 SumExprF where
  liftEq = gliftEq

instance Show1 SumExprF where
  liftShowsPrec = gliftShowsPrec

breakSumExpr :: SumExpr -> [SumExprF Int]
breakSumExpr = cata$ \case
  Val x -> [Val x]
  Plus c1 c2 ->
    let l1 = length c1
        l2 = length c2
    in c1 ++ map (fmap (+ l1)) c2 ++ [Plus (l1 - 1) (l1 + l2 - 1)]

type SumExpr = Fix SumExprF

val :: Int -> SumExpr
val = Fix . Val

(+^+) :: SumExpr -> SumExpr -> SumExpr
(+^+) a b = Fix$ Plus a b

gval :: Int -> SumExprGraph
gval = Fix . Compose . Right . Val

gref :: Int -> SumExprGraph
gref = Fix . Compose . Left

(+.+) :: SumExprGraph -> SumExprGraph -> SumExprGraph
(+.+) a b = Fix$ Compose$ Right$ Plus a b

sumAlg :: SumExprF Int -> Int
sumAlg = \case
  Val x -> x
  Plus x y -> traceShow (x, y)$ x + y

sumExpr_tree :: SumExpr
sumExpr_tree = (val 3 +^+ (val 2 +^+ val 2)) +^+ (val 2 +^+ val 2)

type SumExprGraph = TreeGraph SumExprF Int

unwrap (Fix x) = x

sumExpr_graph :: SumExprGraph
sumExpr_graph = (gval 3 +.+ gref 0) +.+ (gval 3 +.+ gref 0)

sumExpr_graph_fromRef :: Int -> SumExprGraph
sumExpr_graph_fromRef 0 = gval 2 +.+ gval 2

type MyState = State (Maybe Int)

sumExpr_graph_fromRef'
  :: Int -> (SumExprGraph, MyState (Maybe Int), Int -> MyState ())
sumExpr_graph_fromRef' _ = (gval 2 +.+ gval 2, get, put . Just)

run :: Int
run = evalState
  (treeDag_cataM_unsorted sumExpr_graph_fromRef' (return . sumAlg) sumExpr_graph)
  Nothing
