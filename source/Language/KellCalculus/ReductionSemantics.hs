{-#
  LANGUAGE
  UnicodeSyntax,
  PostfixOperators
  #-}

module Language.KellCalculus.ReductionSemantics
    ((↝), subReduce,
     (/↝), isInNormalForm,
     δ, υ, ψ,
    reduce) where

import Data.Foldable
import Data.Maybe
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import qualified Data.Set as Set

import Language.Common.SetLike

import Language.KellCalculus.AST

when :: Bool -> a -> Maybe a
when True x = Just x
when False _ = Nothing

(↝) :: Pattern pl ⇒ Process pl → Maybe (Process pl)
-- SR.Ctx
(↝) r = traverseEC sr r
    -- SR.Kell
    where sr (Kell b (Restriction a p) q) =
              when (Set.null (a ∩ (freeNames b ∪ freeNames q)))
                   (Restriction a (Kell b p q))
          -- SR.GC
          sr (Restriction a p) = when (Set.null (a ∩ freeNames p)) p
          -- SR.Par.L
          sr (ParallelComposition (Restriction a p) q) =
              when (Set.null (a ∩ freeNames q))
                   (Restriction a (ParallelComposition p q))
          -- SR.Par.R
          sr (ParallelComposition q (Restriction a p)) =
              when (Set.null (a ∩ freeNames q))
                   (Restriction a (ParallelComposition q p))
          -- FIXME: missing SR.α
          sr p = Just p
subReduce :: Pattern pl ⇒ Process pl → Maybe (Process pl)
subReduce = (↝)

(/↝) :: Pattern pl ⇒ Process pl → Bool
(/↝) p = isNothing (p ↝)
isInNormalForm :: Pattern pl ⇒ Process pl → Bool
isInNormalForm = (/↝)
-- FIXME: Use this when the related bug is fixed:
--        http://ghc.haskell.org/trac/ghc/ticket/7650
-- (↝̷) = isInNormalForm

δ :: Pattern ξ ⇒ MultiSet (Process ξ) → (MultiSet (AnnotatedMessage ξ), MultiSet (Process ξ))
δ s = foldMap (\(Message a p q) → (MultiSet.singleton (LocalMessage a p),
                                    MultiSet.singleton q))
              s
υ :: Pattern ξ ⇒ MultiSet (Process ξ) → (MultiSet (AnnotatedMessage ξ), MultiSet (Process ξ))
υ s = foldMap (\(Kell a p q) → (MultiSet.singleton (KellMessage a p),
                                 MultiSet.singleton q))
              s
ψ :: Pattern ξ ⇒ MultiSet (Process ξ) → (MultiSet (AnnotatedMessage ξ), MultiSet (Process ξ))
ψ s = foldMap (\(Kell a p q) → let (md, v) = δ (toMultiSet p) in
                               (MultiSet.map (\(LocalMessage b r) → DownMessage b r a) md,
                                MultiSet.singleton (Kell a (Data.Foldable.foldr composeProcesses NullProcess v) q)))
               s

reduce :: Pattern ξ ⇒ Process ξ → Maybe (Process ξ)
-- R.Red.L
reduce (ParallelComposition (Trigger ξ p) u) =
    let (m, v) = δ (toMultiSet u)
        subst = match ξ m in
    if Set.null subst
    then Nothing
    else Just (Data.Foldable.foldr composeProcesses (substitute p (chooseSubstitution subst)) v)
-- R.Red.G
reduce (ParallelComposition (Kell b (ParallelComposition (Trigger ξ p) u) t)
                            u4) =
    let (m, v) = δ (toMultiSet u)
        (m4, v4) = δ (toMultiSet u4)
        subst = match ξ (m ∪ (MultiSet.map (\(LocalMessage a q) → UpMessage a q b) m4)) in
    if Set.null subst
    then Nothing
    else Just (Data.Foldable.foldr composeProcesses
                     (Kell b
                           (Data.Foldable.foldr composeProcesses
                                  (substitute p (chooseSubstitution subst))
                                  v)
                           t)
                     v4)
-- remaining cases
reduce _ = Nothing
