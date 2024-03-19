{-# LANGUAGE PostfixOperators #-}
{-# LANGUAGE UnicodeSyntax #-}

module Language.KellCalculus.ReductionSemantics
  ( (↝),
    subReduce,
    (/↝),
    δ,
    υ,
    ψ,
    reduce,
  )
where

import Data.Foldable
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import qualified Data.Set as Set
import Language.Common.SetLike
import Language.KellCalculus.AST

when :: Bool -> a -> Maybe a
when True x = Just x
when False _ = Nothing

(↝) :: (Pattern ξ) => Process ξ -> Maybe (Process ξ)
-- SR.Ctx
(↝) r = traverseEC sr r
  where
    -- SR.Kell
    sr (Kell b (Restriction a p) q) =
      when
        (Set.null (a ∩ (freeNames b ∪ freeNames q)))
        (Restriction a (Kell b p q))
    -- SR.GC
    sr (Restriction a p) = when (Set.null (a ∩ freeNames p)) p
    -- SR.Par.L
    sr (ParallelComposition (Restriction a p) q) =
      when
        (Set.null (a ∩ freeNames q))
        (Restriction a (ParallelComposition p q))
    -- SR.Par.R
    sr (ParallelComposition q (Restriction a p)) =
      when
        (Set.null (a ∩ freeNames q))
        (Restriction a (ParallelComposition q p))
    -- FIXME: missing SR.α
    sr p = Just p

subReduce :: (Pattern ξ) => Process ξ -> Maybe (Process ξ)
subReduce = (↝)

(/↝) :: (Pattern ξ) => Process ξ -> Process ξ
(/↝) p = case (p ↝) of
  Just p' -> (p' /↝)
  Nothing -> p

-- FIXME: Use this when the related bug is fixed:
--        http://ghc.haskell.org/trac/ghc/ticket/7650
-- (↝̷) = (/↝)

δ :: (Pattern ξ) => MultiSet (Process ξ) -> (MultiSet (AnnotatedMessage ξ), MultiSet (Process ξ))
δ s =
  foldMap
    ( \j -> case j of
        Message a p q ->
          ( MultiSet.singleton (LocalMessage a p),
            MultiSet.singleton q
          )
        _ -> ((∅), (∅))
    )
    s

υ :: (Pattern ξ) => MultiSet (Process ξ) -> (MultiSet (AnnotatedMessage ξ), MultiSet (Process ξ))
υ s =
  foldMap
    ( \j -> case j of
        Kell a p q ->
          ( MultiSet.singleton (KellMessage a p),
            MultiSet.singleton q
          )
        _ -> ((∅), (∅))
    )
    s

ψ :: (Pattern ξ) => MultiSet (Process ξ) -> (MultiSet (AnnotatedMessage ξ), MultiSet (Process ξ))
ψ s =
  foldMap
    ( \j -> case j of
        Kell a p q ->
          let (md, v) = δ (toMultiSet p)
           in ( MultiSet.map (\(LocalMessage b r) -> DownMessage b r a) md,
                MultiSet.singleton (Kell a (Data.Foldable.foldr composeProcesses NullProcess v) q)
              )
        _ -> ((∅), (∅))
    )
    s

-- | Partitions processes into three multisets:
--
-- 1. messages
-- 2. kells
-- 3. also kells
--
--   discarding anything else. These are used as inputs for the predicates `δ`,
--  `υ`, and `ψ`, respectively.
partitionProcesses ::
  (Pattern ξ) =>
  Process ξ ->
  (MultiSet (Process ξ), MultiSet (Process ξ), MultiSet (Process ξ))
partitionProcesses p@(Message _ _ _) = (MultiSet.singleton p, (∅), (∅))
partitionProcesses p@(Kell _ _ _) =
  ((∅), MultiSet.singleton p, MultiSet.singleton p)
partitionProcesses (ParallelComposition p q) =
  (\(p1, p2, p3) (q1, q2, q3) -> (p1 ∪ q1, p2 ∪ q2, p3 ∪ q3))
    (partitionProcesses p)
    (partitionProcesses q)
partitionProcesses _ = ((∅), (∅), (∅))

reduce :: (Pattern ξ) => Process ξ -> Maybe (Process ξ)
-- R.Red.L
reduce (ParallelComposition (Trigger ξ p) u) =
  let (u1, u2, u3) = partitionProcesses u
      (mm, v1) = δ u1
      (mk, v2) = υ (MultiSet.map (/↝) u2)
      (md, v3) = ψ u3
      θ = match ξ (mm ∪ md ∪ mk)
   in if Set.null θ
        then Nothing
        else
          Just
            ( Data.Foldable.foldr
                composeProcesses
                (substitute p (chooseSubstitution θ))
                (v1 ∪ v2 ∪ v3)
            )
-- R.Red.G
reduce
  ( ParallelComposition
      (Kell b (ParallelComposition (Trigger ξ p) u) t)
      u4
    ) =
    let (u1, u2, u3) = partitionProcesses u
        (mm, v1) = δ u1
        (mk, v2) = υ (MultiSet.map (/↝) u2)
        (md, v3) = ψ u3
        (m, v4) = δ (toMultiSet u4)
        θ = match ξ (mm ∪ md ∪ mk ∪ (MultiSet.map (\(LocalMessage a q) -> UpMessage a q b) m))
     in if Set.null θ
          then Nothing
          else
            Just
              ( Data.Foldable.foldr
                  composeProcesses
                  ( Kell
                      b
                      ( Data.Foldable.foldr
                          composeProcesses
                          (substitute p (chooseSubstitution θ))
                          (v1 ∪ v2 ∪ v3)
                      )
                      t
                  )
                  v4
              )
-- remaining cases
reduce _ = Nothing
