{-# LANGUAGE UnicodeSyntax #-}

module Language.KellCalculus.PnpJKCalculus () where

import qualified Data.Map as Map
import qualified Data.MultiSet as MultiSet
import qualified Data.Set as Set
import Language.Common.SetLike
import Language.KellCalculus.AST
import Language.KellCalculus.Parser
import Text.Derp

class SubPattern ξ where
  matchR :: ξ -> Process PnpJKPattern -> Maybe (Substitution PnpJKPattern)

data MessageTag = Local | Up | Down
  deriving (Eq, Ord, Show)

messageTag :: Parser Char MessageTag
messageTag = (terS "up" ==> const Up) <|> (terS "down" ==> const Down)

data P'
  = P'Variable Variable
  | P'P P
  | P'Message Name P'
  | Blank
  deriving (Eq, Ord, Show)

instance ProtoTerm P' where
  P'Variable _ ≣ P'Variable _ = True
  P'P (PMessage a p) ≣ P'P (PMessage b q) = a ≣ b ∧ p ≣ q
  P'P (PParallelComposition p q) ≣ P'P (PParallelComposition r s) =
    P'P p ≣ P'P r ∧ P'P q ≣ P'P s
  P'Message a p ≣ P'Message b q = a ≣ b ∧ p ≣ q
  Blank ≣ Blank = True
  _ ≣ _ = False

p' :: Parser Char P'
p' =
  (bindingTok <~> identifier ==> (\(_, x) -> P'Variable (Variable x)))
    <|> (p ==> P'P)
    <|> ( startMessageTok
            |~| bindingTok
            <~> name
            >~< p'
            |~| endMessageTok
            ==> (\(_, (_, (a, (p, _)))) -> P'Message a p)
        )
    <|> (ter '_' ==> const Blank)

data P
  = PMessage Name P'
  | PParallelComposition P P
  deriving (Eq, Ord, Show)

p :: Parser Char P
p =
  ( startMessageTok
      |~| name
      >~< p'
      |~| endMessageTok
      ==> (\(_, (a, (q, _))) -> PMessage a q)
  )
    <|> ( startFormTok
            |~| parTok
            <~> starw p
            |~| endFormTok
            ==> (\(_, (_, (ps, _))) -> foldr1 PParallelComposition ps)
        )

data J
  = JMessage MessageTag Name P'
  | JParallelComposition J J
  deriving (Eq, Ord, Show)

j :: Parser Char J
j =
  ( startFormTok
      |~| messageTag
      >~< startMessageTok
      |~| name
      >~< p'
      |~| endMessageTok
      |~| endFormTok
      ==> (\(_, (tag, (_, (a, (p, _))))) -> JMessage tag a p)
  )
    <|> ( startMessageTok
            |~| name
            >~< p'
            |~| endMessageTok
            ==> (\(_, (a, (p, _))) -> JMessage Local a p)
        )
    <|> ( startFormTok
            |~| parTok
            <~> starw j
            |~| endFormTok
            ==> (\(_, (_, (p, _))) -> foldr1 JParallelComposition p)
        )

data KellMessage = JKellMessage Name Variable
  deriving (Eq, Ord, Show)

kellMessage :: Parser Char KellMessage
kellMessage =
  startKellTok
    |~| name
    >~< bindingTok
    <~> identifier
    |~| endKellTok
    ==> (\(_, (a, (_, (x, _)))) -> JKellMessage a (Variable x))

data PnpJKPattern
  = J J
  | JKKellMessage KellMessage
  | JKParallelComposition J KellMessage
  deriving (Eq, Ord, Show)

instance MultiSettable PnpJKPattern where
  toMultiSet m@(J JMessage {}) = MultiSet.singleton m
  toMultiSet (J (JParallelComposition ξ1 ξ2)) =
    toMultiSet (J ξ1) ∪ toMultiSet (J ξ2)
  toMultiSet k@(JKKellMessage _) = MultiSet.singleton k
  toMultiSet (JKParallelComposition ξ k) =
    MultiSet.insert (JKKellMessage k) (toMultiSet (J ξ))

instance SubPattern P' where
  matchR Blank _ = Just (Substitution Map.empty Map.empty)
  matchR (P'Variable x) p = Just (Substitution Map.empty (Map.singleton x p))
  matchR (P'P p) q = matchR p q
  matchR (P'Message a p') (Message b p NullProcess) =
    combine
      <$> sequenceA
        [ Just (Substitution (Map.singleton a b) Map.empty),
          matchR p' p
        ]
  matchR (P'Message _ _) _ = error "Can not match a message against a non-message"

toPattern :: P -> PnpJKPattern
toPattern p = J (toJ p)
  where
    toJ (PMessage a q) = JMessage Local a q
    toJ (PParallelComposition q r) = JParallelComposition (toJ q) (toJ r)

instance SubPattern P where
  -- would be nice to not throw away other matches at this level
  matchR p q =
    let subst = match (toPattern p) (toAnnotatedMessages q)
     in if Set.null subst
          then Nothing
          else Just (chooseSubstitution subst)

instance NQTerm PnpJKPattern where
  freeNames (J (JMessage _ a p)) =
    Set.insert a (freeNamesP p)
    where
      freeNamesP (P'Variable _) = (∅)
      freeNamesP (P'P (PMessage b q)) = Set.insert b (freeNamesP q)
      freeNamesP (P'P (PParallelComposition q r)) =
        freeNamesP (P'P q) ∪ freeNamesP (P'P r)
      freeNamesP (P'Message _ q) = freeNamesP q
      freeNamesP Blank = (∅)
  freeNames (J (JParallelComposition p q)) =
    freeNames (J p) ∪ freeNames (J q)
  freeNames (JKKellMessage (JKellMessage a _)) = Set.singleton a
  freeNames (JKParallelComposition p k) =
    freeNames (J p) ∪ freeNames (JKKellMessage k)

instance ProtoTerm PnpJKPattern where
  J (JMessage tag1 a p) ≣ J (JMessage tag2 b q) =
    tag1 == tag2 ∧ a ≣ b ∧ p ≣ q
  JKKellMessage (JKellMessage a _) ≣ JKKellMessage (JKellMessage b _) = a ≣ b
  JKParallelComposition ξ k ≣ JKParallelComposition ζ k' =
    J ξ ≣ J ζ ∧ JKKellMessage k ≣ JKKellMessage k'
  _ ≣ _ = False

instance Pattern PnpJKPattern where
  matchM (J (JMessage Local a p)) (LocalMessage b q) =
    if a == b then matchR p q else Nothing
  matchM (J (JMessage Down a p)) (DownMessage b q _) =
    if a == b then matchR p q else Nothing
  matchM (J (JMessage Up a p)) (UpMessage b q _) =
    if a == b then matchR p q else Nothing
  matchM (JKKellMessage (JKellMessage a x)) (KellMessage b p) =
    if a == b
      then Just (Substitution Map.empty (Map.singleton x p))
      else Nothing
  matchM _ _ = error "Can not matchM these two processes."
  boundNames (J (JMessage _ a p)) =
    Set.insert a (boundNamesP p)
    where
      boundNamesP (P'Variable _) = (∅)
      boundNamesP (P'P (PMessage _ p)) = boundNamesP p
      boundNamesP (P'P (PParallelComposition p q)) =
        boundNamesP (P'P p) ∪ boundNamesP (P'P q)
      boundNamesP (P'Message a p) = Set.insert a (boundNamesP p)
      boundNamesP Blank = (∅)
  boundNames (J (JParallelComposition p q)) =
    boundNames (J p) ∪ boundNames (J q)
  boundNames (JKKellMessage (JKellMessage _ _)) = (∅)
  boundNames (JKParallelComposition p k) =
    boundNames (J p) ∪ boundNames (JKKellMessage k)
  boundVariables (J (JMessage _ _ p)) =
    boundVariablesP p
    where
      boundVariablesP (P'Variable x) = Set.singleton x
      boundVariablesP (P'P (PMessage _ p)) = boundVariablesP p
      boundVariablesP (P'P (PParallelComposition p q)) =
        boundVariablesP (P'P p) ∪ boundVariablesP (P'P q)
      boundVariablesP (P'Message _ p) = boundVariablesP p
      boundVariablesP Blank = (∅)
  boundVariables (J (JParallelComposition p q)) =
    boundVariables (J p) ∪ boundVariables (J q)
  boundVariables (JKKellMessage (JKellMessage _ x)) = Set.singleton x
  boundVariables (JKParallelComposition p k) =
    boundVariables (J p) ∪ boundVariables (JKKellMessage k)
  sk (J (JMessage _ a _)) = MultiSet.singleton a
  sk (J (JParallelComposition p q)) = sk (J p) ∪ sk (J q)
  sk (JKKellMessage (JKellMessage a _)) = MultiSet.singleton a
  sk (JKParallelComposition p k) = sk (J p) ∪ sk (JKKellMessage k)
  grammar =
    (j ==> J)
      <|> (kellMessage ==> JKKellMessage)
      <|> ( startFormTok
              |~| parTok
              <~> starw j
              >~< kellMessage
              |~| endFormTok
              ==> (\(_, (_, (j, (k, _)))) -> JKParallelComposition (foldr1 JParallelComposition j) k)
          )
