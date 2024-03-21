{-# LANGUAGE Safe #-}

module Language.Common.SetLike
  ( (∈),
    (∉),
    SetLike (..),
    MultiSettable (..),
    (∧),
  )
where

-- import Control.Applicative.Unicode
import Data.Bool (Bool)
import Data.Bool.Unicode ((∧))
import Data.Foldable.Unicode ((∈), (∉))
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import Data.Ord (Ord)
import Data.Set (Set)
import qualified Data.Set as Set

class SetLike sl where
  (∅) :: sl t
  (∩) :: (Ord t) => sl t -> sl t -> sl t
  (∪) :: (Ord t) => sl t -> sl t -> sl t
  (∖) :: (Ord t) => sl t -> sl t -> sl t
  (⊂) :: (Ord t) => sl t -> sl t -> Bool
  (⊆) :: (Ord t) => sl t -> sl t -> Bool

instance SetLike Set where
  (∅) = Set.empty
  (∩) = Set.intersection
  (∪) = Set.union
  (∖) = Set.difference
  (⊂) = Set.isProperSubsetOf
  (⊆) = Set.isSubsetOf

instance SetLike MultiSet where
  (∅) = MultiSet.empty
  (∩) = MultiSet.intersection
  (∪) = MultiSet.union
  (∖) = MultiSet.difference
  (⊂) = MultiSet.isProperSubsetOf
  (⊆) = MultiSet.isSubsetOf

class MultiSettable ms where
  -- this “flattens” a pattern to a multiset. Whereas a full pattern may have
  -- a complex structure of compositions, etc. to enforce various constraints,
  -- this gives us a set of the top-level patterns more directly.
  toMultiSet :: ms -> MultiSet ms
