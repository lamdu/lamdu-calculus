-- TODO: This shouldn't be in lamdu-calculus, which only even uses `match`.

{-# LANGUAGE NoImplicitPrelude #-}
module Data.Map.Utils
    ( lookupOrSelf, pop, popKeys, matchKeys, match, differenceSet
    ) where

import           Prelude.Compat

import qualified Control.Lens as Lens
import           Control.Lens.Operators
import           Control.Monad (guard)
import           Control.Monad.Trans.State (StateT(..))
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Set (Set)

differenceSet :: Ord k => Map k a -> Set k -> Map k a
differenceSet m = Map.difference m . Map.fromSet (const ())

lookupOrSelf :: Ord a => Map a a -> a -> a
lookupOrSelf m x = fromMaybe x $ m ^. Lens.at x

pop :: Ord k => k -> Map k v -> Maybe (v, Map k v)
pop k m =
    Map.lookup k m <&> f
    where
        f v = (v, Map.delete k m)

popKeys :: (Traversable t, Ord k) => t k -> Map k v -> Maybe (t v, Map k v)
popKeys = runStateT . traverse (StateT . pop)

matchKeys :: (Traversable t, Ord k) => t k -> Map k v -> Maybe (t v)
matchKeys keys m = do
    (vals, rest) <- popKeys keys m
    guard $ Map.null rest
    return vals

match :: Ord k => (a -> b -> c) -> Map k a -> Map k b -> Maybe (Map k c)
match valMatch m0 m1
    | Map.keysSet m0 == Map.keysSet m1 =
          Just $ Map.intersectionWith valMatch m0 m1
    | otherwise = Nothing
