{-# LANGUAGE UnicodeSyntax #-}

module Language.KellCalculus.ContextualEquivalence ((↓)) where

import Language.Common.SetLike
import Language.KellCalculus.AST

(↓) :: (Pattern ξ) => Process ξ -> Name -> Bool
Restriction c p ↓ a = (a ∉ c) && (p ↓ a)
Message b _ _ ↓ a = b ≣ a
ParallelComposition p q ↓ a = p ↓ a || q ↓ a
Kell c (Kell b _ _) _ ↓ a = b ≣ a || c ≣ a
Kell b _ _ ↓ a = b ≣ a
_ ↓ _ = False
