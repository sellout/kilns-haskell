{-#
  LANGUAGE
  UnicodeSyntax,
  PostfixOperators
  #-}

module Language.KellCalculus.AST
    (Process(..),
     AnnotatedMessage(..),
     Substitution(..),
     Variable(..),
     Name(..),
     NQTerm(..), ProtoTerm(..), Term(..),
     MultiSettable(..), Pattern(..),
     AnyContext(..), Hole(..),
     match, combine, substitute, composeProcesses,
     toAnnotatedMessages, chooseSubstitution, traverseEC
     ) where

import Data.Foldable
import Data.Functor
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Data.MultiSet (MultiSet)
import qualified Data.MultiSet as MultiSet
import Data.Set (Set)
import qualified Data.Set as Set
import Text.Derp (Parser)

import Language.Common.SetLike

class Ord t ⇒ NQTerm t where
    freeNames :: t → Set Name

class ProtoTerm t where
    -- structural congruence
    (≣) :: t → t → Bool

class (NQTerm t, ProtoTerm t) ⇒ Term t where
    freeVariables :: t → Set Variable

data Name = Name String deriving (Eq, Ord, Show)

instance NQTerm Name where
    freeNames a = Set.singleton a

instance ProtoTerm Name where
    (Name a) ≣ (Name b) = a == b

instance Term Name where
    freeVariables _ = (∅)

data Variable = Variable String deriving (Eq, Ord, Show)

instance ProtoTerm Variable where
    (Variable a) ≣ (Variable b) = a == b

data Process ξ
    = NullProcess
    | ProcessVariable Variable
    | Trigger ξ (Process ξ)
    | Restriction (Set Name) (Process ξ)
    | Message Name (Process ξ) (Process ξ)
    | ParallelComposition (Process ξ) (Process ξ)
    | Kell Name (Process ξ) (Process ξ)
    deriving (Eq, Ord, Show)

instance Pattern ξ ⇒ NQTerm (Process ξ) where
    freeNames NullProcess = (∅)
    freeNames (ProcessVariable _) = (∅)
    freeNames (Restriction a p) = freeNames p ∖ a
    freeNames (Kell a q p) = freeNames a ∪ freeNames q ∪ freeNames p
    freeNames (Message a p q) = freeNames a ∪ freeNames p ∪ freeNames q
    freeNames (ParallelComposition p q) = freeNames p ∪ freeNames q
    freeNames (Trigger ξ p) = freeNames ξ ∪ (freeNames p ∖ boundNames ξ)

instance Pattern ξ ⇒ ProtoTerm (Process ξ) where
    -- structural congruence
    -- S.Par.A
    ParallelComposition (ParallelComposition p1 q1) r1
                      ≣ ParallelComposition p2 (ParallelComposition q2 r2) =
                          p1 ≣ p2 ∧ q1 ≣ q2 ∧ r1 ≣ r2
    -- S.Par.C
    ParallelComposition p1 q1 ≣ ParallelComposition q2 p2 = p1 ≣ p2 ∧ q1 ≣ q2
    -- S.Par.N
    ParallelComposition p1 NullProcess ≣ p2 = p1 ≣ p2
    -- S.Nu.Nil
    Restriction _ NullProcess ≣ NullProcess = True
    -- S.Nu.C
    Restriction a1 (Restriction b1 p1) ≣ Restriction b2 (Restriction a2 p2) =
        a1 == a2 ∧ b1 == b2 ∧ p1 ≣ p2
    -- S.Nu.Par
    ParallelComposition (Restriction a1 p1) q1
                      ≣ Restriction a2 (ParallelComposition p2 q2) =
                          a1 == a2 ∧ p1 ≣ p2 ∧ q1 ≣ q2 ∧ Set.null (a2 ∩ freeNames q2)
    -- S.Nu.Kell
    Kell b1 (Restriction a1 p1) q1 ≣ Restriction a2 (Kell b2 p2 q2) =
        a1 == a2 ∧ b1 == b2 ∧ p1 ≣ p2 ∧ q1 ≣ q2 ∧ Set.null (a2 ∩ (freeNames b2 ∪ freeNames q2))
    -- S.Trig
    Trigger ξ p1 ≣ Trigger ζ p2 = p1 ≣ p2 ∧ ξ ≣ ζ
    -- S.a
    p ≣ q = p == q
    -- S.Context

instance Pattern ξ ⇒ Term (Process ξ) where
    freeVariables NullProcess = (∅)
    freeVariables (ProcessVariable x) = Set.singleton x
    freeVariables (Restriction _ p) = freeVariables p
    freeVariables (Kell _ q p) = freeVariables q ∪ freeVariables p
    freeVariables (Message _ p q) = freeVariables p ∪ freeVariables q
    freeVariables (ParallelComposition p q) = freeVariables p ∪ freeVariables q
    freeVariables (Trigger ξ p) = freeVariables p ∖ boundVariables ξ

instance Pattern ξ ⇒ MultiSettable (Process ξ) where
    toMultiSet (ParallelComposition p q) = toMultiSet p ∪ toMultiSet q
    toMultiSet p = MultiSet.singleton p

-- this should keep processes is some normal-ish form, where we treat
-- ParallelComposition as a Cons
composeProcesses :: Pattern ξ ⇒ Process ξ → Process ξ → Process ξ
composeProcesses p NullProcess = p
composeProcesses NullProcess p = p
composeProcesses (ParallelComposition p q) c@(ParallelComposition _ _) =
    composeProcesses p (composeProcesses q c)
composeProcesses p c@(ParallelComposition _ _) = ParallelComposition p c
composeProcesses c@(ParallelComposition _ _) p = ParallelComposition p c
composeProcesses p q = ParallelComposition p q

data AnnotatedMessage ξ
    = LocalMessage Name (Process ξ)
    | UpMessage Name (Process ξ) Name
    | DownMessage Name (Process ξ) Name
    | KellMessage Name (Process ξ)
    deriving (Eq, Ord)

instance Pattern ξ ⇒ NQTerm (AnnotatedMessage ξ) where
    freeNames (LocalMessage a p) = freeNames a ∪ freeNames p
    -- TODO: should the source kell name be free or not?
    freeNames (UpMessage a p _) = freeNames a ∪ freeNames p
    freeNames (DownMessage a p _) = freeNames a ∪ freeNames p
    freeNames (KellMessage a p) = freeNames a ∪ freeNames p

instance Pattern ξ ⇒ ProtoTerm (AnnotatedMessage ξ) where
    (LocalMessage a p) ≣ (LocalMessage b q) = a ≣ b ∧ p ≣ q
    (UpMessage a p k) ≣ (UpMessage b q l) = a ≣ b ∧ p ≣ q ∧ k ≣ l
    (DownMessage a p k) ≣ (DownMessage b q l) = a ≣ b ∧ p ≣ q ∧ k ≣ l
    (KellMessage a p) ≣ (KellMessage b q) = a ≣ b ∧ p ≣ q
    _ ≣ _ = False

instance Pattern ξ ⇒ Term (AnnotatedMessage ξ) where
    freeVariables (LocalMessage a p) = freeVariables a ∪ freeVariables p
    freeVariables (UpMessage a p _) = freeVariables a ∪ freeVariables p
    freeVariables (DownMessage a p _) = freeVariables a ∪ freeVariables p
    freeVariables (KellMessage a p) = freeVariables a ∪ freeVariables p

class AnyContext c where
    fillHole :: c ξ → Process ξ → Process ξ

data Hole ξ = Hole

instance AnyContext Hole where
    fillHole Hole p = p

data Context ξ
    = HoleC (Hole ξ)
    | TriggerC ξ (Context ξ)
    | RestrictionC (Set Name) (Context ξ)
    | ParallelCompositionC (Process ξ) (Context ξ)
    | KellStateHoleC Name (Context ξ) (Process ξ)
    | MessageArgHoleC Name (Context ξ) (Process ξ)
    | MessageContHoleC Name (Process ξ) (Context ξ)
    | KellContHoleC Name (Process ξ) (Context ξ)

instance AnyContext Context where
    fillHole (HoleC c)                  p = fillHole c p
    fillHole (TriggerC ξ c)             p = Trigger ξ (fillHole c p)
    fillHole (RestrictionC a c)         p = Restriction a (fillHole c p)
    fillHole (ParallelCompositionC p c) q = ParallelComposition p (fillHole c q)
    fillHole (KellStateHoleC a c q)     p = Kell a (fillHole c p) q
    fillHole (MessageArgHoleC a c q)    p = Message a (fillHole c p) q
    fillHole (MessageContHoleC a p c)   q = Message a p (fillHole c q)
    fillHole (KellContHoleC a p c)      q = Kell a p (fillHole c q)

data ExecutionContext ξ
    = HoleEC (Hole ξ)
    | RestrictionEC (Set Name) (ExecutionContext ξ)
    | KellEC Name (ExecutionContext ξ) (Process ξ)
    | ParallelCompositionEC (Process ξ) (ExecutionContext ξ)

instance AnyContext ExecutionContext where
    fillHole (HoleEC c)                  p = fillHole c p
    fillHole (RestrictionEC a c)         p = Restriction a (fillHole c p)
    fillHole (KellEC a c q)              p = Kell a (fillHole c p) q
    fillHole (ParallelCompositionEC p c) q = ParallelComposition p (fillHole c q)

andThen :: Maybe a → Maybe a → Maybe a
x `andThen` y = case x of
                  Just _ → y
                  Nothing → Nothing

traverseEC :: Pattern ξ ⇒
             (Process ξ → Maybe (Process ξ)) → Process ξ → Maybe (Process ξ)
traverseEC f (Restriction a p) =
    let sub = traverseEC f p in sub `andThen` f (Restriction a (Maybe.fromJust sub))
traverseEC f (Kell a p q) =
    let sub = traverseEC f p in sub `andThen` f (Kell a (Maybe.fromJust sub) q)
traverseEC f (ParallelComposition p q) =
    let sub1 = traverseEC f p
        sub2 = traverseEC f q in
    case sub1 of
      Just p' → case sub2 of
                  Just q' → f (ParallelComposition p' q')
                  Nothing → f (ParallelComposition p' q)
      Nothing → case sub2 of
                  Just q' → f (ParallelComposition p q')
                  Nothing → Nothing
traverseEC f p = f p

-- data ExecutionContextTree ξ = Leaf (Process ξ)
--                             | Branch (ExecutionContext ξ)
--                                      [ExecutionContextTree ξ]

-- extractTerms :: Pattern ξ ⇒ Process ξ → ExecutionContextTree ξ
-- extractTerms p = Branch (HoleEC Hole) (p : subExtractTerms p)
--     where subExtractTerms (Restriction a p) =
--               [Branch (RestrictionEC a Hole) (Leaf p : subExtractTerms p)]
--           subExtractTerms (Kell a p q) =
--               [Branch (KellEC a Hole q) (Leaf p : subExtractTerms p)]
--           subExtractTerms (ParallelComposition p q) =
--               [Branch (ParallelCompositionEC p Hole)
--                       (Leaf q : subExtractTerms q),
--                Branch (ParallelCompositionEC q Hole)
--                       (Leaf p : subExtractTerms p)]

data Substitution ξ = Substitution (Map Name Name) (Map Variable (Process ξ))
                    deriving (Eq, Ord)

class (MultiSettable ξ, NQTerm ξ, ProtoTerm ξ, Show ξ) ⇒ Pattern ξ where
    matchM :: ξ → AnnotatedMessage ξ → Maybe (Substitution ξ)
    boundNames :: ξ → Set Name
    boundVariables :: ξ → Set Variable
    sk :: ξ → MultiSet Name
    grammar :: Parser Char ξ

combine :: Pattern ξ ⇒ [Substitution ξ] → Substitution ξ
combine (Substitution nm1 vm1:Substitution nm2 vm2:ses) =
    combine (Substitution (Map.union nm1 nm2) (Map.union vm1 vm2) : ses)
combine [s] = s
combine [] = error "Can not combine zero substitutions"
 
-- this is useful if you want to use match farther down in a pattern match
toAnnotatedMessages :: Pattern ξ ⇒ Process ξ → MultiSet (AnnotatedMessage ξ)
toAnnotatedMessages (ParallelComposition p q)
    = toAnnotatedMessages p ∪ toAnnotatedMessages q
toAnnotatedMessages (Message a p _) = MultiSet.singleton (LocalMessage a p) -- _ or NullProcess?
toAnnotatedMessages NullProcess = MultiSet.empty
toAnnotatedMessages _ = error "This process can not be converted to a multiset of annotated messages."
 
-- TODO: the paper seems to indicate that this will be called with the same
--       number of patterns & annotated messages, but how is that possible? I
--       feel like there are just _at least_ as many annotated messages as
--       patterns.
match :: Pattern ξ ⇒ ξ → MultiSet (AnnotatedMessage ξ) → Set (Substitution ξ)
match ξr m = let ξrs = MultiSet.elems (toMultiSet ξr)
                 ms = MultiSet.elems m
                 js = [0, 1 .. List.length ξrs - 1] in
             Set.fromList (Maybe.catMaybes (map (\σ → combine <$> sequence (map (\j → matchM (ξrs !! j)
                                                                                               (ms !! (σ !! j)))
                                                                                 js))
                                                (List.permutations js)))

-- ensure `toSet (sk ξ) ⊆ freeNames ξ`
-- ensure `when ξ ≣ ζ
--         then freeNames ξ = freeNames ζ
--           ∧ sk ξ = sk ζ
--           ∧ (boundNames ξ ∪ boundVariables ξ)
--              = (boundNames ζ ∪ boundVariables ζ)`

substitute :: Pattern ξ ⇒ Process ξ → Substitution ξ → Process ξ
substitute p θ@(Substitution nm vm) =
    case p of
      NullProcess → NullProcess
      ProcessVariable x → case Map.lookup x vm of
                            Just q → q
                            Nothing → p
      Trigger ξ q →
          Trigger ξ
                  (substitute q
                              (Substitution (removeFromMap nm (boundNames ξ))
                                            (removeFromMap vm (boundVariables ξ))))
      Restriction a q →
          Restriction a (substitute q (Substitution (removeFromMap nm a) vm))
      Message a q r → Message (substName a) (substitute q θ) (substitute r θ)
      ParallelComposition q r →
          ParallelComposition (substitute q θ) (substitute r θ)
      Kell a q r → Kell (substName a) (substitute q θ) (substitute r θ)
    where substName a = case Map.lookup a nm of
                          Just b → b
                          Nothing → a
          removeFromMap m a = Data.Foldable.foldr Map.delete m a

-- this allows us to configure how we select a substitution from the set of
-- possibilities
chooseSubstitution :: Pattern ξ ⇒ Set (Substitution ξ) → (Substitution ξ)
chooseSubstitution = Set.findMin
