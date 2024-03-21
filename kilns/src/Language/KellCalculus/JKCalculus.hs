{-# LANGUAGE Unsafe #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Language.KellCalculus.JKCalculus
  ( JKPattern (..),
    J,
    KellMessage,
  )
where

import safe Data.Bool (Bool (False))
import safe Data.Char (Char)
import safe Data.Eq (Eq ((==)))
import safe Data.Foldable (Foldable (foldr1))
import safe Data.Function (const)
import safe qualified Data.Map as Map
import safe Data.Maybe (Maybe (Just, Nothing))
import safe qualified Data.MultiSet as MultiSet
import safe Data.Ord (Ord)
import safe Data.Semigroup (Semigroup ((<>)))
import safe qualified Data.Set as Set
import safe Language.Common.SetLike (MultiSettable (toMultiSet), SetLike ((∅), (∪)), (∧))
import safe Language.KellCalculus.AST
  ( AnnotatedMessage (DownMessage, KellMessage, LocalMessage, UpMessage),
    NQTerm (freeNames),
    Name,
    Pattern (boundNames, boundVariables, grammar, matchM, sk),
    ProtoTerm ((≣)),
    Substitution (Substitution),
    Variable,
  )
import Language.KellCalculus.Parser
  ( SexpSyntax (SexpSyntax),
    bindingTok,
    endFormTok,
    endKellTok,
    endMessageTok,
    name,
    parTok,
    startFormTok,
    startKellTok,
    startMessageTok,
    starw,
    variable,
    (>~<),
    (|~|),
  )
import safe Text.Derp (Parser)
import Text.Derp.Unsafe (terS, (<|>), (<~>), (==>))
import safe Text.Show (Show (show))
import safe Prelude (error)

data MessageTag = Local | Up | Down
  deriving stock (Eq, Ord, Show)

messageTag :: Parser Char MessageTag
messageTag = (terS "up" ==> const Up) <|> (terS "down" ==> const Down)

data J
  = JMessage MessageTag Name Variable
  | JParallelComposition J J
  deriving stock (Eq, Ord, Show)

instance Show (SexpSyntax J) where
  show (SexpSyntax ξ) =
    case ξ of
      JMessage Local n v -> "{" <> show (SexpSyntax n) <> " " <> show (SexpSyntax v) <> "}"
      JMessage Up n v -> "(up " <> show (SexpSyntax (JMessage Local n v)) <> ")"
      JMessage Down n v -> "(down " <> show (SexpSyntax (JMessage Local n v)) <> ")"
      JParallelComposition j j' ->
        show (SexpSyntax j)
          <> " "
          <> show (SexpSyntax j')

j :: Parser Char J
j =
  ( startFormTok
      |~| messageTag
      >~< startMessageTok
      |~| name
      >~< variable
      |~| endMessageTok
      |~| endFormTok
      ==> (\(_, (tag, (_, (a, (p, _))))) -> JMessage tag a p)
  )
    <|> ( startMessageTok
            |~| name
            >~< variable
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
  deriving stock (Eq, Ord, Show)

instance Show (SexpSyntax KellMessage) where
  show (SexpSyntax (JKellMessage n v)) =
    "[" <> show (SexpSyntax n) <> " " <> show (SexpSyntax v) <> "]"

kellMessage :: Parser Char KellMessage
kellMessage =
  startKellTok
    |~| name
    >~< bindingTok
    <~> variable
    |~| endKellTok
    ==> (\(_, (a, (_, (x, _)))) -> JKellMessage a x)

data JKPattern
  = J J
  | JKKellMessage KellMessage
  | JKParallelComposition J KellMessage
  deriving stock (Eq, Ord, Show)

instance Show (SexpSyntax JKPattern) where
  show (SexpSyntax ξ) =
    case ξ of
      J j -> show (SexpSyntax j)
      JKKellMessage k -> show (SexpSyntax k)
      JKParallelComposition j k ->
        "(par "
          <> show (SexpSyntax j)
          <> " "
          <> show (SexpSyntax k)
          <> ")"

instance NQTerm JKPattern where
  freeNames (J (JMessage _ a _)) = Set.singleton a
  freeNames (J (JParallelComposition ξ1 ξ2)) =
    freeNames (J ξ1) ∪ freeNames (J ξ2)
  freeNames (JKKellMessage (JKellMessage a _)) = Set.singleton a
  freeNames (JKParallelComposition ξ (JKellMessage a _)) =
    Set.insert a (freeNames (J ξ))

instance ProtoTerm JKPattern where
  J (JMessage tag1 a _) ≣ J (JMessage tag2 b _) = tag1 == tag2 ∧ a ≣ b
  JKKellMessage (JKellMessage a _) ≣ JKKellMessage (JKellMessage b _) = a ≣ b
  JKParallelComposition ξ k ≣ JKParallelComposition ζ k' =
    J ξ ≣ J ζ ∧ JKKellMessage k ≣ JKKellMessage k'
  _ ≣ _ = False

instance MultiSettable JKPattern where
  toMultiSet m@(J JMessage {}) = MultiSet.singleton m
  toMultiSet (J (JParallelComposition ξ1 ξ2)) =
    toMultiSet (J ξ1) ∪ toMultiSet (J ξ2)
  toMultiSet k@(JKKellMessage _) = MultiSet.singleton k
  toMultiSet (JKParallelComposition ξ k) =
    MultiSet.insert (JKKellMessage k) (toMultiSet (J ξ))

instance Pattern JKPattern where
  matchM (J (JMessage Local a x)) (LocalMessage b p) =
    if a == b
      then Just (Substitution Map.empty (Map.singleton x p))
      else Nothing
  matchM (J (JMessage Up a x)) (UpMessage b p _) =
    if a == b
      then Just (Substitution Map.empty (Map.singleton x p))
      else Nothing
  matchM (J (JMessage Down a x)) (DownMessage b p _) =
    if a == b
      then Just (Substitution Map.empty (Map.singleton x p))
      else Nothing
  matchM (JKKellMessage (JKellMessage a x)) (KellMessage b p) =
    if a == b
      then Just (Substitution Map.empty (Map.singleton x p))
      else Nothing
  matchM _ _ = error "Can not matchM these two processes."
  boundNames _ = (∅)
  boundVariables (J (JMessage _ _ x)) = Set.singleton x
  boundVariables (J (JParallelComposition ξ1 ξ2)) =
    boundVariables (J ξ1) ∪ boundVariables (J ξ2)
  boundVariables (JKKellMessage (JKellMessage _ x)) = Set.singleton x
  boundVariables (JKParallelComposition ξ (JKellMessage _ x)) =
    Set.insert x (boundVariables (J ξ))
  sk (J (JMessage _ a _)) = MultiSet.singleton a
  sk (J (JParallelComposition ξ1 ξ2)) = sk (J ξ1) ∪ sk (J ξ2)
  sk (JKKellMessage (JKellMessage a _)) = MultiSet.singleton a
  sk (JKParallelComposition ξ (JKellMessage a _)) =
    MultiSet.insert a (sk (J ξ))
  grammar =
    (j ==> J)
      <|> (kellMessage ==> JKKellMessage)
      <|> ( startFormTok
              |~| parTok
              <~> starw j
              >~< kellMessage
              |~| endFormTok
              ==> (\(_, (_, (js, (k, _)))) -> JKParallelComposition (foldr1 JParallelComposition js) k)
          )
