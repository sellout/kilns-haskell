{-#
  LANGUAGE
  UnicodeSyntax,
  PostfixOperators
  #-}

module Language.KellCalculus.LabeledTransitionSystem
    (Concretion(..), Abstraction(..), Action(..), Agent(..),
     compose, papp, commit) where

import Data.Foldable
import Data.Functor
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import Data.Set (Set)
import qualified Data.Set as Set

import Language.Common.SetLike

import Language.KellCalculus.AST
import Language.KellCalculus.ReductionSemantics

data Concretion pl
    = Concretion (Set Name) (MultiSet (AnnotatedMessage pl)) (Process pl)
    deriving (Eq, Ord)

instance Pattern pl ⇒ NQTerm (Concretion pl) where
    freeNames (Concretion a ω p) =
        (Data.Foldable.foldr (∪)
               (∅)
               (MultiSet.map (\am → case am of
                                      LocalMessage b q → freeNames b ∪ freeNames q
                                      UpMessage b q c → freeNames b ∪ freeNames q  ∪ freeNames c
                                      DownMessage b q c → freeNames b ∪ freeNames q  ∪ freeNames c
                                      KellMessage b q → freeNames b ∪ freeNames q)
                            ω) ∪ freeNames p) ∖ a

instance Pattern pl ⇒ ProtoTerm (Concretion pl) where
    Concretion a ω p ≣ Concretion b ω' q = a == b ∧ ω == ω' ∧ p ≣ q

instance Pattern pl ⇒ Term (Concretion pl) where
    freeVariables (Concretion _ ω p) =
        (Data.Foldable.foldr (∪)
               (∅)
               (MultiSet.map (\am → case am of
                                      LocalMessage _ q → freeVariables q
                                      UpMessage _ q _ → freeVariables q
                                      DownMessage _ q _ → freeVariables q
                                      KellMessage _ q → freeVariables q)
                            ω) ∪ freeVariables p)


data SimpleAbstraction pl
    = PatternAbstraction pl (Process pl)
    | SimpleApplicationAbstraction (SimpleAbstraction pl) (Concretion pl)
    deriving (Eq, Ord)

data Abstraction pl
    = SimpleAbstraction (SimpleAbstraction pl)
    | KellAbstraction Name (SimpleAbstraction pl) (Process pl)
    | ApplicationAbstraction (Abstraction pl) (Concretion pl)
    | RestrictionAbstraction (Set Name) (Abstraction pl)
    deriving (Eq, Ord)

instance Pattern pl ⇒ NQTerm (Abstraction pl) where
    freeNames (SimpleAbstraction (PatternAbstraction ξ p)) =
        freeNames ξ ∪ (freeNames p ∖ boundNames ξ)
    freeNames (SimpleAbstraction (SimpleApplicationAbstraction a c)) =
        freeNames (SimpleAbstraction a) ∪ freeNames c
    freeNames (KellAbstraction a p q) =
        freeNames a ∪ freeNames (SimpleAbstraction p) ∪ freeNames q
    freeNames (ApplicationAbstraction a c) = freeNames a ∪ freeNames c
    freeNames (RestrictionAbstraction a p) = freeNames p ∖ a

instance Pattern pl ⇒ ProtoTerm (Abstraction pl) where
    (SimpleAbstraction (PatternAbstraction ξ p)) ≣ (SimpleAbstraction (PatternAbstraction ζ q)) =
        ξ ≣ ζ ∧ p ≣ q
    SimpleAbstraction (SimpleApplicationAbstraction a c) ≣ SimpleAbstraction (SimpleApplicationAbstraction a' c') =
        SimpleAbstraction a ≣ SimpleAbstraction a' ∧ c ≣ c'
    KellAbstraction a p q ≣ KellAbstraction a' p' q' =
        a == a' ∧ SimpleAbstraction p ≣ SimpleAbstraction p' ∧ q ≣ q'
    ApplicationAbstraction a c ≣ ApplicationAbstraction a' c' = a ≣ a' ∧ c ≣ c'
    RestrictionAbstraction a p ≣ RestrictionAbstraction a' q = a == a' ∧ p ≣ q
    _ ≣ _ = False

instance Pattern pl ⇒ Term (Abstraction pl) where
    freeVariables (SimpleAbstraction (PatternAbstraction ξ p)) =
        freeVariables p ∖ boundVariables ξ
    freeVariables (SimpleAbstraction (SimpleApplicationAbstraction a c)) =
        freeVariables (SimpleAbstraction a) ∪ freeVariables c
    freeVariables (KellAbstraction _ p q) =
        freeVariables (SimpleAbstraction p) ∪ freeVariables q
    freeVariables (ApplicationAbstraction a c) =
        freeVariables a ∪ freeVariables c
    freeVariables (RestrictionAbstraction _ p) = freeVariables p

data Action
    = Complete
    | Silent
    | Receive Name
    | Send Name
    | Composition Action Action
    deriving (Eq, Ord)

instance NQTerm Action where
    freeNames Complete = (∅)
    freeNames Silent = (∅)
    freeNames (Receive n) = Set.singleton n
    freeNames (Send n) = Set.singleton n
    freeNames (Composition m n) = freeNames m ∪ freeNames n

-- TODO: determine if all actions should just be in a multiset instead of using
--       Composition
instance MultiSettable Action where
    toMultiSet (Composition m n) = toMultiSet m ∪ toMultiSet n
    toMultiSet a = MultiSet.singleton a

data Agent pl
    = ProcessA (Process pl)
    | AbstractionA (Abstraction pl)
    | ConcretionA (Concretion pl)
    deriving (Eq, Ord)

concretionFrom :: Pattern pl ⇒ Agent pl → Concretion pl
concretionFrom (ConcretionA c) = c
concretionFrom _ = error "Not a concretion"

instance Pattern pl ⇒ NQTerm (Agent pl) where
    freeNames (ProcessA p) = freeNames p
    freeNames (AbstractionA f) = freeNames f
    freeNames (ConcretionA c) = freeNames c

instance Pattern pl ⇒ ProtoTerm (Agent pl) where
    -- structural congruence
    (ProcessA p) ≣ (ProcessA q) = p ≣ q
    (AbstractionA f) ≣ (AbstractionA f') = f ≣ f'
    (ConcretionA c) ≣ (ConcretionA c') = c ≣ c'
    _ ≣ _ = False

instance Pattern pl ⇒ Term (Agent pl) where
    freeVariables (ProcessA p) = freeVariables p
    freeVariables (AbstractionA f) = freeVariables f
    freeVariables (ConcretionA c) = freeVariables c

compose :: Pattern pl ⇒ Agent pl → Agent pl → Maybe (Agent pl)
compose (ProcessA p) (ProcessA q) = Just (ProcessA (composeProcesses p q))
compose (AbstractionA f) (ProcessA q) =
    Just (AbstractionA (ApplicationAbstraction f (Concretion (∅) (∅) q)))
compose (ConcretionA (Concretion a ω p)) (ProcessA q) =
    if a ∩ freeNames q == (∅)
    then Just (ConcretionA (Concretion a ω (ParallelComposition p q)))
    else Nothing
compose (ConcretionA (Concretion a ω p)) (ConcretionA (Concretion c ω' p')) =
    if a ∩ (foldMap freeNames ω' ∪ freeNames p') == (∅)
       ∧ c ∩ (foldMap freeNames ω ∪ freeNames p) == (∅)
    then Just (ConcretionA (Concretion (a ∪ c) (ω ∪ ω') (ParallelComposition p p')))
    else Nothing
compose _ _ = Nothing

-- pseudo-application
papp :: Pattern pl ⇒ Abstraction pl → Concretion pl → Maybe (Process pl)
papp (ApplicationAbstraction f c) c' =
    papp f =<< concretionFrom <$> (compose (ConcretionA c) (ConcretionA c'))
papp (SimpleAbstraction (PatternAbstraction ξ r)) (Concretion a ω p) =
    if Set.null a
    then let θs = match ξ ω in
         if Set.null θs
         then Nothing
         else Just (ParallelComposition (substitute r (chooseSubstitution θs)) p)
    else Nothing
papp (KellAbstraction a
                      (SimpleApplicationAbstraction (PatternAbstraction ξ r)
                                                    (Concretion _ ω p))
                      t)
     (Concretion _ mm q) =
    let θs = match ξ (ω ∪ MultiSet.map (\(LocalMessage b s) → UpMessage b s a) mm) in
    if Set.null θs
    then Nothing
    else Just (ParallelComposition (Kell a (ParallelComposition (substitute r (chooseSubstitution θs)) p) t) q)
papp (RestrictionAbstraction a f) (Concretion b c p) =
    if Set.null (a ∩ Data.Foldable.foldr (∪) (∅) (MultiSet.map freeNames c)) ∧ Set.null (b ∩ freeNames f)
    then Restriction (a ∪ b) <$> papp f (Concretion (∅) c p)
    else Nothing
papp _ _ = Nothing

commit :: Pattern ξ ⇒ Process ξ → Action → Maybe (Agent ξ)
-- T.Mess
commit (Message a1 p q) (Receive a2) =
    if a1 == a2
    then Just (ConcretionA (Concretion (∅) (MultiSet.singleton (LocalMessage a1 p)) q))
    else Nothing
-- T.Kell
commit k@(Kell a1 p q) (Receive a2) = if a1 == a2 ∧ (k /↝)
                                      then Just (ConcretionA (Concretion (∅) (MultiSet.singleton (KellMessage a1 p)) q))
                                      else Nothing
-- T.Trig
commit (Trigger ξ p) α =
    if MultiSet.map Receive (sk ξ) == toMultiSet α
    then Just (AbstractionA (SimpleAbstraction (PatternAbstraction ξ p)))
    else Nothing
-- T.New
commit (Restriction a p) α = if α /= Complete ∧ Set.null (a ∩ freeNames α)
                             then case commit p α of
                                    Just (AbstractionA agent) → Just (AbstractionA (RestrictionAbstraction a agent))
                                    Just _ → Nothing
                                    Nothing → Nothing
                             else Nothing
-- T.Kell.C, .F, .P
commit k@(Kell a p r) α =
    if (k /↝)
    then case commit p α of
           Just (ConcretionA (Concretion b mm q)) →
                if Set.null b
                then Just (ConcretionA (Concretion (∅)
                                                   (MultiSet.map (\(LocalMessage c s) → DownMessage c s a)
                                                                 mm)
                                                   (Kell a q r)))
                else Nothing
           Just (AbstractionA (SimpleAbstraction g)) →
               Just (AbstractionA (KellAbstraction a g r))
           Just (ProcessA q) → Just (ProcessA (Kell a q r))
           Just _ → Nothing
           Nothing → Nothing
    else Nothing
-- T.Par.FC
commit par@(ParallelComposition p q) (Composition α β) =
    if (par /↝)
    then case α of
           Complete → Nothing
           _ → case sequence [commit p α, commit q β] of
                 Just x -> Data.Foldable.foldrM compose (ProcessA NullProcess) x
                 Nothing -> Nothing
    else Nothing
-- T.Par.L, .R
commit par@(ParallelComposition p q) α =
    if (par /↝)
    then case α of
           Complete → Nothing
           _ → case commit p α of
                 Just a → compose a (ProcessA q)
                 Nothing → case commit p α of
                             Just a → compose a (ProcessA q)
                             Nothing → Nothing
    else Nothing
-- T.Par.CC

-- T.Red
commit p Silent = commit p Complete
-- T.SR
commit p α = case (p ↝) of
               Just q → commit q α
               Nothing → Nothing
-- T.α
