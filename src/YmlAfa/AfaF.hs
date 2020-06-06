{-# LANGUAGE DeriveFunctor, DeriveTraversable, DeriveFoldable, FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module YmlAfa.AfaF where

import Debug.Trace

import Control.Arrow ((&&&))
import Control.Monad
import Control.Monad.State.Lazy
import Data.Either
import Data.Functor.Foldable
import qualified Data.Functor.Foldable as RS
import Data.Functor.Compose
import Data.Foldable

import Data.Array.IArray


type TreeGraphF f ref = Compose (Either ref) f
type TreeGraph f ref = Fix (TreeGraphF f ref)

type Formula = Fix FormulaF


toTree
  :: Functor f
  => (ref -> TreeGraph f ref)
  -> TreeGraph f ref
  -> Fix f
toTree fromRef = cata$ \case
  Compose (Left ref) -> toTree fromRef$ fromRef ref
  Compose (Right x) -> Fix x


cachedCata
  :: forall f m ref a. (Traversable f, Monad m)
  => (ref -> (TreeGraph f ref, m (Maybe a), a -> m ()))
  -> (f a -> a)
  -> TreeGraph f ref
  -> m a
cachedCata fromRef algebra = helper where
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
    return$ algebra x'


cachedCata_bottomUp
  :: (Functor f, Ix ix, Ix ix, IArray arr a, Functor (arr ix))
  => (f a -> a)
  -> [TreeGraph f ix]  -- ^ must be topologically sorted
  -> (ix, ix)
  -> arr ix a
cachedCata_bottomUp alg xs bounds = result where
  result = listArray bounds$ flip map xs$ cata$ \case
    Compose (Left ref) -> result ! ref
    Compose (Right x) -> alg x

-- examples ----------------------------------------------------------------------------

data FormulaF rec
  = And [rec]
  | Or [rec]
  | Not rec
  | Q Int
  | A Int
  | T
  | F
  deriving (Functor, Foldable, Traversable)

data SumExprF rec
  = Val Int
  | Plus rec rec
  deriving (Functor, Foldable, Traversable, Show)

breakSumExpr :: SumExpr -> [SumExprF Int]
breakSumExpr = cata$ \case
  Val x -> [Val x]
  Plus c1 c2 ->
    let l1 = length c1
        l2 = length c2
    in c1 ++ map (fmap (+ l1)) c2 ++ [Plus (l1 - 1) (l1 + l2 - 1)]


breakF :: forall f. (Traversable f) => Fix f -> [f Int]
breakF = cata alg where
  alg :: f [f Int] -> [f Int]
  alg node
    | null childs = [fmap undefined node]
    | otherwise = concat childs' ++ [node']
    where
      node' = evalState (traverse (\_ -> state (head &&& tail)) node) offsets

      childs = toList node
      lengths = map length childs
      offsets = scanl (+) 0 lengths
      childs' = zipWith (\o -> map$ fmap (+ o)) offsets childs


type TerminalOrParts f a = Either [f (Either Int (f a))] (f a)

-- | This is a parallelizable yet less efficient version of "breakF'state"
breakF' :: forall f a. (Traversable f) => Fix f -> TerminalOrParts f a
breakF' = cata alg where
  alg :: f (TerminalOrParts f a) -> TerminalOrParts f a
  alg node
    | null childs = Right (fmap undefined node)
    | otherwise = Left (concat (lefts childs') ++ [node'])
    where
      node' :: f (Either Int (f a))
      node' = evalState (traverse (\x -> state (setRef x . head &&& tail)) node) offsets

      setRef :: TerminalOrParts f a -> Int -> Either Int (f a)
      setRef (Right terminal) o = Right terminal
      setRef (Left _) o = Left o

      childs = toList node :: [TerminalOrParts f a]

      lengths :: [Int]
      lengths = flip map childs$ \case
        Left terminal -> 0
        Right parts -> length parts

      offsets = scanl (+) 0 lengths

      childs' :: [TerminalOrParts f a]
      childs' = zipWith offsetRefs offsets childs

      offsetRefs :: Int -> TerminalOrParts f a -> TerminalOrParts f a
      offsetRefs o = \case
        x@(Right _) -> x
        (Left childs) -> Left$ flip map childs$ fmap$ \case
          (Left ref) -> Left$ ref + o
          x@_ -> x

type TerminalOrParts' f a = Either (Int, [f (Either Int (f a))]) (f a)

breakF'state :: forall f a. (Traversable f)
  => Fix f -> State Int (TerminalOrParts' f a)
breakF'state tree = cataM alg tree where
  alg :: f (TerminalOrParts' f a) -> State Int (TerminalOrParts' f a)
  alg node
    | null childs = return$ Right (fmap undefined node)
    | otherwise = do
      ix <- state$ id &&& succ
      return$ Left (ix, concat (map snd$ lefts childs) ++ [node'])
    where
      node' :: f (Either Int (f a))
      node' = fmap setRef node

      setRef (Right terminal) = Right terminal
      setRef (Left (ix, _)) = Left ix

      childs = toList node :: [TerminalOrParts' f a]


type RefOrTerminal f a = Either Int (f a)

cataM :: (Monad m, Traversable (Base t), Recursive t)
  => (Base t a -> m a) -> t ->  m a
cataM alg = c where
  c = alg <=< traverse c . project

breakAlg :: (Functor f, Foldable f)
  => f (RefOrTerminal f a)
  -> Either (f (RefOrTerminal f a)) (f a)
breakAlg node
  | null (toList node) = Right (fmap undefined node)
  | otherwise = Left node

collect
  :: Either (f (RefOrTerminal f a)) (f a)
  -> State (Int, [f (RefOrTerminal f a)]) (RefOrTerminal f a)
collect (Right x) = return$ Right x
collect (Left node) = do
  i <- state$ \(i, nodes) -> (i, (i + 1, node : nodes))
  return$ Left i

breakF'collect :: (Traversable (Base t), Recursive t)
  => t
  -> State (Int, [(Base t) (RefOrTerminal (Base t) a)]) (RefOrTerminal (Base t) a)
breakF'collect = cataM (collect . breakAlg)

breakF'monad :: forall f a. (Traversable f)
  => Fix f -> State Int (TerminalOrParts' f a)
breakF'monad tree = cataM alg tree where
  alg :: f (TerminalOrParts' f a) -> State Int (TerminalOrParts' f a)
  alg node
    | null childs = return$ Right (fmap undefined node)
    | otherwise = do
      ix <- state$ id &&& succ
      return$ Left (ix, concat (map snd$ lefts childs) ++ [node'])
    where
      node' :: f (Either Int (f a))
      node' = fmap setRef node

      setRef (Right terminal) = Right terminal
      setRef (Left (ix, _)) = Left ix

      childs = toList node :: [TerminalOrParts' f a]


type SumExpr = Fix SumExprF

val :: Int -> SumExpr
val = Fix . Val

(+++) :: SumExpr -> SumExpr -> SumExpr
(+++) a b = Fix$ Plus a b

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

foo :: SumExpr
foo = val 3 +++ val 4

sumExpr_tree :: SumExpr
sumExpr_tree = (val 3 +++ (val 2 +++ val 2)) +++ (val 2 +++ val 2)

type SumExprGraph = TreeGraph SumExprF Int

unwrap (Fix x) = x

sumExpr_graph :: SumExprGraph
sumExpr_graph = ((gval 3 +.+ gval 4) +.+ (gref 0)) +.+ (gref 0)

sumExpr_graph_fromRef :: Int -> SumExprGraph
sumExpr_graph_fromRef 0 = gval 2 +.+ gval 2

type MyState = State (Maybe Int)

sumExpr_graph_fromRef'
  :: Int -> (SumExprGraph, MyState (Maybe Int), Int -> MyState ())
sumExpr_graph_fromRef' _ = (gval 2 +.+ gval 2, get, put . Just)

run :: Int
run = evalState (cachedCata sumExpr_graph_fromRef' sumAlg sumExpr_graph) Nothing
