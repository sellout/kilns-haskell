{-# LANGUAGE Unsafe #-}

module Language.KellCalculus.Parser
  ( process,
    name,
    variable,
    identifier,
    startKellTok,
    endKellTok,
    startMessageTok,
    endMessageTok,
    startFormTok,
    endFormTok,
    parTok,
    nullTok,
    bindingTok,
    (>~<),
    (|~|),
    starw,
    star1w,
    SexpSyntax (..),
  )
where

import safe Control.Category (Category ((.)))
import safe Data.Char (Char)
import safe qualified Data.CharSet as CharSet
import safe qualified Data.CharSet.Unicode.Category as Unicode
import safe Data.Eq (Eq ((==)))
import safe Data.Foldable (Foldable (toList))
import safe Data.Function (const, ($))
import safe Data.Functor (Functor (fmap), (<$>))
import safe qualified Data.List as List
import safe Data.List.NonEmpty (NonEmpty ((:|)))
import safe Data.Maybe (Maybe (Just, Nothing), catMaybes, fromMaybe, maybe)
import safe Data.Monoid (Monoid (mconcat))
import safe Data.Ord (Ord ((<=)))
import safe Data.Semigroup (Semigroup ((<>)))
import safe Data.Semigroup.Foldable (Foldable1 (fold1))
import safe qualified Data.Set as Set
import safe Data.String (String)
import safe Data.Tuple (fst, snd, uncurry)
import Language.Common.SetLike (SetLike ((∪)))
import safe Language.KellCalculus.AST
  ( Name (Name),
    Pattern,
    Process
      ( Kell,
        Message,
        NullProcess,
        ParallelComposition,
        ProcessVariable,
        Restriction,
        Trigger
      ),
    Variable (Variable),
  )
import safe Text.Derp (Parser)
import Text.Derp.Unsafe
  ( option,
    star,
    star1,
    ter,
    terM,
    terS,
    (<|>),
    (<~>),
    (==>),
  )
import safe Text.Show (Show (show))
import safe Prelude (error)

whitespaceChar :: Parser Char ()
whitespaceChar = terM (Set.fromList (CharSet.toList Unicode.separator) ∪ Set.fromList ['\n']) ==> const ()

legalChar :: Parser Char String
legalChar =
  terM
    ( Set.fromList (CharSet.toList Unicode.separator)
        ∪ Set.fromList (CharSet.toList Unicode.letter)
        ∪ Set.fromList (CharSet.toList Unicode.symbol)
        ∪ Set.fromList (CharSet.toList Unicode.number)
        ∪ Set.fromList (CharSet.toList Unicode.punctuation)
    )

-- Really want to keep this in the AST, but just toss it for now
comment :: Parser Char String
comment = star1 (ter ';') <~> star legalChar <~> ter '\n' ==> mconcat . fst . snd

maybeComment :: Parser Char (Maybe String)
maybeComment = whitespaceChar ==> const Nothing <|> comment ==> Just

whitespace :: Parser Char [String]
whitespace = star1 maybeComment ==> catMaybes . toList

whitespace' :: Parser Char [String]
whitespace' = star maybeComment ==> catMaybes

-- required whitespace
(>~<) :: (Ord a, Ord b) => Parser Char a -> Parser Char b -> Parser Char (a, b)
a >~< b = a <~> whitespace <~> b ==> (\(x, (_, y)) -> (x, y))

-- optional whitespace
(|~|) :: (Ord a, Ord b) => Parser Char a -> Parser Char b -> Parser Char (a, b)
a |~| b = a <~> whitespace' <~> b ==> (\(x, (_, y)) -> (x, y))

infixr 3 >~<

infixr 3 |~|

optionw :: (Ord a) => Parser Char a -> Parser Char (Maybe a)
optionw p = option (whitespace <~> p) ==> (<$>) snd

starw :: (Ord a) => Parser Char a -> Parser Char [a]
starw p = star (whitespace <~> p) ==> fmap snd

star1w :: (Ord a) => Parser Char a -> Parser Char (NonEmpty a)
star1w p = p <~> starw p ==> uncurry (:|)

startKellTok :: Parser Char String
startKellTok = ter '['

endKellTok :: Parser Char String
endKellTok = ter ']'

startMessageTok :: Parser Char String
startMessageTok = ter '{'

endMessageTok :: Parser Char String
endMessageTok = ter '}'

startFormTok :: Parser Char String
startFormTok = ter '('

endFormTok :: Parser Char String
endFormTok = ter ')'

parTok :: Parser Char String
parTok = terS "par"

triggerTok :: Parser Char String
triggerTok = terS "trigger"

restrictionTok :: Parser Char String
restrictionTok = terS "new"

nullTok :: Parser Char String
nullTok = terS "null"

contTok :: Parser Char String
contTok = terS "cont"

bindingTok :: Parser Char String
bindingTok = ter '?'

identifier :: Parser Char String
identifier =
  terM (Set.fromList (CharSet.toList Unicode.letter))
    <~> star (terM (Set.fromList (CharSet.toList Unicode.letter)))
    ==> (\(h, rest) -> mconcat (h : rest))

-- (complement [startKellTok, endKellTok,
--              startMessageTok, endMessageTok,
--              startFormTok, endFormTok])

newtype SexpSyntax a = SexpSyntax {getSexpSyntax :: a}

instance (Eq a) => Eq (SexpSyntax a) where
  SexpSyntax l == SexpSyntax r = l == r

instance (Ord a) => Ord (SexpSyntax a) where
  SexpSyntax l <= SexpSyntax r = l <= r

name :: Parser Char Name
name = identifier ==> Name

instance Show (SexpSyntax Name) where
  show (SexpSyntax (Name ident)) = ident

variable :: Parser Char Variable
variable = identifier ==> Variable

instance Show (SexpSyntax Variable) where
  show (SexpSyntax (Variable ident)) = ident

nullProcess :: (Pattern ξ) => Parser Char (Process ξ)
nullProcess = nullTok ==> const NullProcess

processVariable :: (Pattern ξ) => Parser Char (Process ξ)
processVariable = variable ==> ProcessVariable

addContinuation :: (Pattern ξ) => Process ξ -> Process ξ -> Process ξ
addContinuation (Kell a q NullProcess) cont = Kell a q cont
addContinuation (Kell a q r) cont = Kell a q (addContinuation r cont)
addContinuation (Message a q NullProcess) cont = Message a q cont
addContinuation (Message a q r) cont = Message a q (addContinuation r cont)
addContinuation _ _ = error "Impossible continuation application."

continuation :: (Pattern ξ) => Parser Char ξ -> Parser Char (Process ξ)
continuation ξ =
  startFormTok |~| contTok
    >~< (kell ξ <|> message ξ)
    >~< process ξ |~| endFormTok
    ==> \(_, (_, (p, (cont, _)))) -> addContinuation p cont

kell :: (Pattern ξ) => Parser Char ξ -> Parser Char (Process ξ)
kell ξ =
  startKellTok |~| name >~< process ξ <~> optionw (process ξ) <~> endKellTok
    ==> (\(_, (a, (q, (p, _)))) -> Kell a q (fromMaybe NullProcess p))

message :: (Pattern ξ) => Parser Char ξ -> Parser Char (Process ξ)
message ξ =
  startMessageTok
    |~| name <~> optionw (process ξ <~> optionw (process ξ)) <~> endMessageTok
    ==> ( \(_, (a, (p, _))) ->
            uncurry (Message a) $
              maybe (NullProcess, NullProcess) (fmap $ fromMaybe NullProcess) p
        )

trigger :: (Pattern ξ) => Parser Char ξ -> Parser Char (Process ξ)
trigger ξ =
  startFormTok |~| triggerTok >~< ξ >~< process ξ <~> endFormTok
    ==> (\(_, (_, (pat, (proc, _)))) -> Trigger pat proc)

restriction :: (Pattern ξ) => Parser Char ξ -> Parser Char (Process ξ)
restriction ξ =
  startFormTok |~| restrictionTok >~< name >~< process ξ <~> endFormTok
    ==> (\(_, (_, (a, (p, _)))) -> Restriction (Set.singleton a) p)

parallelComposition :: (Pattern ξ) => Parser Char ξ -> Parser Char (Process ξ)
parallelComposition ξ =
  startFormTok |~| parTok >~< star1w (process ξ) <~> endFormTok
    ==> (\(_, (_, (p, _))) -> fold1 p)

process :: (Pattern ξ) => Parser Char ξ -> Parser Char (Process ξ)
process ξ =
  whitespace'
    <~> ( nullProcess
            <|> processVariable
            <|> trigger ξ
            <|> restriction ξ
            <|> message ξ
            <|> parallelComposition ξ
            <|> kell ξ
            <|> continuation ξ
        )
    <~> whitespace'
    ==> fst . snd

instance (Pattern ξ, Show (SexpSyntax ξ)) => Show (SexpSyntax (Process ξ)) where
  show (SexpSyntax k) =
    case k of
      NullProcess -> "null"
      ProcessVariable var -> show (SexpSyntax var)
      Trigger ξ p ->
        "(trigger "
          <> show (SexpSyntax ξ)
          <> " "
          <> show (SexpSyntax p)
          <> ")"
      Restriction a p ->
        "(new ("
          <> List.unwords (fmap (show . SexpSyntax) (Set.toList a))
          <> ") "
          <> show (SexpSyntax p)
          <> ")"
      Message a NullProcess NullProcess -> "{" <> show (SexpSyntax a) <> "}"
      Message a p NullProcess ->
        "{" <> show (SexpSyntax a) <> " " <> show (SexpSyntax p) <> "}"
      Message a p q ->
        "(cont {"
          <> show (SexpSyntax a)
          <> " "
          <> show (SexpSyntax p)
          <> "} "
          <> show (SexpSyntax q)
          <> ")"
      ParallelComposition p q ->
        "(par " <> show (SexpSyntax p) <> " " <> show (SexpSyntax q) <> ")"
      Kell a NullProcess NullProcess -> "[" <> show (SexpSyntax a) <> "]"
      Kell a p NullProcess ->
        "[" <> show (SexpSyntax a) <> " " <> show (SexpSyntax p) <> "]"
      Kell a p q ->
        "(cont ["
          <> show (SexpSyntax a)
          <> " "
          <> show (SexpSyntax p)
          <> "] "
          <> show (SexpSyntax q)
          <> ")"
