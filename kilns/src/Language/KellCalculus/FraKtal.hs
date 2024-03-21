{-# LANGUAGE Unsafe #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- | A pattern language for the kell calculus. It’s like
--  "Language.KellCalculus.PnpJKCalculus", but adds checking and binding of
--  /complements/ of message arguments. This is defined in §5.
module Language.KellCalculus.FraKtal
  ( FraKtal (..),
    J,
    KellMessage,
  )
where

import safe Control.Category (Category ((.)))
import safe Data.Bool (Bool (False, True))
import safe Data.Char (Char)
import safe Data.Eq (Eq ((/=), (==)))
import safe Data.Function (const, ($))
import safe Data.Functor ((<$>))
import safe qualified Data.Map as Map
import safe Data.Maybe (Maybe (Just, Nothing))
import safe qualified Data.MultiSet as MultiSet
import safe Data.Ord (Ord)
import safe Data.Semigroup (Semigroup ((<>)))
import safe Data.Semigroup.Foldable (Foldable1 (fold1))
import safe qualified Data.Set as Set
import safe Data.Tuple (snd)
import safe Language.Common.SetLike (MultiSettable (toMultiSet), SetLike ((∅), (∪)), (∧))
import safe Language.KellCalculus.AST
  ( AnnotatedMessage (DownMessage, KellMessage, LocalMessage, UpMessage),
    NQTerm (freeNames),
    Name,
    Pattern (boundNames, boundVariables, grammar, matchM, sk),
    Process (Message, NullProcess),
    ProtoTerm ((≣)),
    Substitution (Substitution),
    Variable,
    chooseSubstitution,
    match,
    toAnnotatedMessages,
  )
import Language.KellCalculus.Parser
  ( SexpSyntax (SexpSyntax),
    bindingTok,
    endFormTok,
    endKellTok,
    endMessageTok,
    name,
    parTok,
    star1w,
    startFormTok,
    startKellTok,
    startMessageTok,
    variable,
    (>~<),
    (|~|),
  )
import safe Text.Derp (Parser)
import Text.Derp.Unsafe (ter, terS, (<|>), (<~>), (==>))
import safe Text.Show (Show (show))
import safe Prelude (error)

class SubPattern ξ where
  matchR :: ξ -> Process FraKtal -> Maybe (Substitution FraKtal)

data MessageTag = Local | Up | Down
  deriving stock (Eq, Ord, Show)

messageTag :: Parser Char MessageTag
messageTag = terS "up" ==> const Up <|> terS "down" ==> const Down

data P'
  = P'Variable Variable
  | P'P P
  | P'Message Name P'
  | P'Complement Name P'
  | P'BoundComplement Name Name P'
  | Blank
  deriving stock (Eq, Ord, Show)

instance ProtoTerm P' where
  P'Variable _ ≣ P'Variable _ = True
  P'P (PMessage a p) ≣ P'P (PMessage b q) = a ≣ b ∧ p ≣ q
  P'P (PParallelComposition p q) ≣ P'P (PParallelComposition r s) =
    P'P p ≣ P'P r ∧ P'P q ≣ P'P s
  P'Message a p ≣ P'Message b q = a ≣ b ∧ p ≣ q
  P'Complement a p ≣ P'Complement b q = a ≣ b ∧ p ≣ q
  P'BoundComplement a _ p ≣ P'BoundComplement b _ q = a ≣ b ∧ p ≣ q
  Blank ≣ Blank = True
  _ ≣ _ = False

instance Show (SexpSyntax P') where
  show (SexpSyntax ξ) =
    case ξ of
      P'Variable v -> "?" <> show (SexpSyntax v)
      P'P p -> show (SexpSyntax p)
      P'Message n p ->
        "{" <> show (SexpSyntax n) <> " " <> show (SexpSyntax p) <> "}"
      P'Complement n p ->
        "{(/= " <> show (SexpSyntax n) <> ") " <> show (SexpSyntax p) <> "}"
      P'BoundComplement n b p ->
        "{(/= "
          <> show (SexpSyntax n)
          <> " ?"
          <> show (SexpSyntax b)
          <> ") "
          <> show (SexpSyntax p)
          <> "}"
      Blank -> "_"

p' :: Parser Char P'
p' =
  bindingTok <~> variable ==> P'Variable . snd
    <|> p ==> P'P
    <|> startMessageTok |~| bindingTok <~> name >~< p' |~| endMessageTok
      ==> (\(_, (_, (a, (p, _)))) -> P'Message a p)
    <|> startMessageTok |~| startFormTok |~| terS "/="
      >~< name |~| endFormTok
      >~< p' |~| endMessageTok
      ==> (\(_, (_, (_, (a, (_, (p, _)))))) -> P'Complement a p)
    <|> startMessageTok |~| startFormTok |~| terS "/="
      >~< name
      >~< bindingTok <~> name |~| endFormTok
      >~< p' |~| endMessageTok
      ==> ( \(_, (_, (_, (a, (_, (m, (_, (p, _)))))))) ->
              P'BoundComplement m a p
          )
    <|> ter '_' ==> const Blank

data P
  = PMessage Name P'
  | PParallelComposition P P
  deriving stock (Eq, Ord, Show)

instance Semigroup P where
  a@PMessage {} <> b = PParallelComposition a b
  c@PParallelComposition {} <> a@PMessage {} = PParallelComposition a c
  PParallelComposition p q <> PParallelComposition p' q' =
    PParallelComposition p . PParallelComposition p' $ q <> q'

instance Show (SexpSyntax P) where
  show (SexpSyntax ξ) =
    case ξ of
      PMessage n p ->
        "{" <> show (SexpSyntax n) <> " " <> show (SexpSyntax p) <> "}"
      PParallelComposition p q ->
        "(par " <> show (SexpSyntax p) <> " " <> show (SexpSyntax q) <> ")"

p :: Parser Char P
p =
  startMessageTok |~| name >~< p' |~| endMessageTok
    ==> (\(_, (a, (p, _))) -> PMessage a p)
    <|> startFormTok |~| parTok >~< star1w p |~| endFormTok
      ==> (\(_, (_, (p, _))) -> fold1 p)

data J
  = JMessage MessageTag Name P'
  | JParallelComposition J J
  deriving stock (Eq, Ord, Show)

instance Semigroup J where
  a@JMessage {} <> b = JParallelComposition a b
  c@JParallelComposition {} <> a@JMessage {} = JParallelComposition a c
  JParallelComposition p q <> JParallelComposition p' q' =
    JParallelComposition p . JParallelComposition p' $ q <> q'

instance Show (SexpSyntax J) where
  show (SexpSyntax ξ) =
    case ξ of
      JMessage Local n v ->
        "{" <> show (SexpSyntax n) <> " " <> show (SexpSyntax v) <> "}"
      JMessage Up n v -> "(up " <> show (SexpSyntax (JMessage Local n v)) <> ")"
      JMessage Down n v ->
        "(down " <> show (SexpSyntax (JMessage Local n v)) <> ")"
      JParallelComposition j j' ->
        show (SexpSyntax j) <> " " <> show (SexpSyntax j')

j :: Parser Char J
j =
  startFormTok |~| messageTag
    >~< startMessageTok |~| name
    >~< p' |~| endMessageTok |~| endFormTok
    ==> (\(_, (tag, (_, (a, (p, _))))) -> JMessage tag a p)
    <|> startMessageTok |~| name >~< p' |~| endMessageTok
      ==> (\(_, (a, (p, _))) -> JMessage Local a p)
    <|> startFormTok |~| parTok >~< star1w j |~| endFormTok
      ==> (\(_, (_, (p, _))) -> fold1 p)

data KellMessage = JKellMessage Name Variable
  deriving stock (Eq, Ord, Show)

instance Show (SexpSyntax KellMessage) where
  show (SexpSyntax (JKellMessage n v)) =
    "[" <> show (SexpSyntax n) <> " " <> show (SexpSyntax v) <> "]"

kellMessage :: Parser Char KellMessage
kellMessage =
  startKellTok |~| name >~< variable |~| endKellTok
    ==> (\(_, (a, (x, _))) -> JKellMessage a x)

data FraKtal
  = J J
  | JKKellMessage KellMessage
  | JKParallelComposition J KellMessage
  deriving stock (Eq, Ord, Show)

instance Show (SexpSyntax FraKtal) where
  show (SexpSyntax ξ) =
    case ξ of
      J j -> show (SexpSyntax j)
      JKKellMessage k -> show (SexpSyntax k)
      JKParallelComposition j k ->
        "(par " <> show (SexpSyntax j) <> " " <> show (SexpSyntax k) <> ")"

instance MultiSettable FraKtal where
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
    (Substitution (Map.singleton a b) Map.empty <>) <$> matchR p' p
  matchR (P'Complement a p') (Message b p NullProcess) =
    if a /= b then matchR p' p else Nothing
  matchR (P'BoundComplement m a p') (Message b p NullProcess) =
    if a /= b
      then (Substitution (Map.singleton m b) Map.empty <>) <$> matchR p' p
      else Nothing
  matchR _ _ = Nothing

toPattern :: P -> FraKtal
toPattern p = J (toJ p)
  where
    toJ (PMessage a p) = JMessage Local a p
    toJ (PParallelComposition p q) = JParallelComposition (toJ p) (toJ q)

instance SubPattern P where
  -- would be nice to not throw away other matches at this level
  matchR p q =
    let subst = match (toPattern p) (toAnnotatedMessages q)
     in if Set.null subst
          then Nothing
          else Just (chooseSubstitution subst)

instance NQTerm FraKtal where
  freeNames (J (JMessage _ a p)) =
    Set.insert a (freeNamesP p)
    where
      freeNamesP (P'Variable _) = (∅)
      freeNamesP (P'P (PMessage a p)) = Set.insert a (freeNamesP p)
      freeNamesP (P'P (PParallelComposition p q)) =
        freeNamesP (P'P p) ∪ freeNamesP (P'P q)
      freeNamesP (P'Message _ p) = freeNamesP p
      -- FIXME: are these complement names considered free?
      freeNamesP (P'Complement a p) = Set.insert a (freeNamesP p)
      freeNamesP (P'BoundComplement _ a p) = Set.insert a (freeNamesP p)
      freeNamesP Blank = (∅)
  freeNames (J (JParallelComposition p q)) =
    freeNames (J p) ∪ freeNames (J q)
  freeNames (JKKellMessage (JKellMessage a _)) = Set.singleton a
  freeNames (JKParallelComposition p k) =
    freeNames (J p) ∪ freeNames (JKKellMessage k)

instance ProtoTerm FraKtal where
  J (JMessage tag1 a p) ≣ J (JMessage tag2 b q) =
    tag1 == tag2 ∧ a ≣ b ∧ p ≣ q
  JKKellMessage (JKellMessage a _) ≣ JKKellMessage (JKellMessage b _) = a ≣ b
  JKParallelComposition ξ k ≣ JKParallelComposition ζ k' =
    J ξ ≣ J ζ ∧ JKKellMessage k ≣ JKKellMessage k'
  _ ≣ _ = False

instance Pattern FraKtal where
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
      boundNamesP (P'Complement _ p) = boundNamesP p
      boundNamesP (P'BoundComplement a _ p) =
        Set.insert a (boundNamesP p)
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
      boundVariablesP (P'Complement _ p) = boundVariablesP p
      boundVariablesP (P'BoundComplement _ _ p) = boundVariablesP p
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
    j ==> J
      <|> kellMessage ==> JKKellMessage
      <|> startFormTok |~| parTok >~< star1w j >~< kellMessage |~| endFormTok
        ==> (\(_, (_, (js, (k, _)))) -> JKParallelComposition (fold1 js) k)
