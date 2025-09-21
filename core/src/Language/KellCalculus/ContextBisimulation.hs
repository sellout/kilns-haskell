{-# LANGUAGE Safe #-}

module Language.KellCalculus.ContextBisimulation (isClosed) where

import Control.Category (Category ((.)))
import Data.Bool (Bool)
import qualified Data.Set as Set
import Language.KellCalculus.AST (Pattern, Term (freeVariables))
import Language.KellCalculus.LabeledTransitionSystem (Agent)

isClosed :: (Pattern ξ) => Agent ξ -> Bool
isClosed = Set.null . freeVariables

-- data CApplicativeContext ξ
--     = ApplicationCAC (Hole ξ) (Concretion ξ)
--     | KellApplicationCAC Name (Hole ξ) (Process ξ) (Concretion ξ)
--     | NestedApplicationCAC Name (Hole ξ) (Concretion ξ) (Process ξ) (Concretion ξ)

-- instance AnyContext CApplicativeContext where
--     fillHole (ApplicationCAC ac c)         p =
--         ApplicationAbstraction (fillHole ac p) c
--     fillHole (KellApplicationCAC a ac t d) p =
--         ApplicationAbstraction (KellAbstraction a (fillHole ac p) t) d
--     fillHole (NestedApplicationCAC a ac c t d)  p =
--         ApplicationAbstraction (KellAbstraction a
--                                                 (ApplicationAbstraction (fillHole ac p)
--                                                                         c)
--                                                 t)
--                                d

-- data FApplicativeContext ξ
--     = ApplicationFAC (Abstraction ξ) (Hole ξ)
--     | NestedApplicationFAC Name (Abstraction ξ) (Hole ξ) (Process ξ)
--                            (Concretion ξ)
--     | ConcretionFAC (Abstraction ξ) Name (Hole ξ) (Process ξ)
--     | KellConcretionFAC Name (Abstraction ξ) Name (Hole ξ) (Process ξ) (Process ξ)
--                         (Concretion ξ)

-- instance AnyContext FApplicativeContext where
--     fillHole (ApplicationFAC f ac) p =
--         ApplicationAbstraction f (fillHole ac p)
--     fillHole (NestedApplicationFAC a f ac t d) p =
--         ApplicationAbstraction (KellAbstraction a
--                                                 (ApplicationAbstraction f
--                                                                         (fillHole ac p))
--                                                 t)
--                                d
--     fillHole (ConcretionFAC f a ac t) p =
--         ApplicationAbstraction f (KellAbstraction a (fillHole ac p) t)
--     fillHole (KellConcretionFAC a f b ac t s d) p =
--         ApplicationAbstraction (KellAbstraction
--                                 a
--                                 (ApplicationAbstraction
--                                  f
--                                  (KellAbstraction b (fillHole ac p) t))
--                                 s)
--                                d
