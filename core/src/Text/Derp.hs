{-# LANGUAGE Safe #-}
-- __TODO__: Need to determine exactly where we need laziness annotations before
--           enabling this.
{-# LANGUAGE NoStrictData #-}

module Text.Derp
  ( -- * Data Types
    Parser (..),
    ParserRec (..),
    ContextR (..),
    Token (..),
    ParserRecType (..),
    FPValue (..),

    -- * Parser computation steps
    derive,
    compact,

    -- * Full parsing and result extraction
    defaultCompactSteps,
    compactNum,
    deriveStepNum,
    deriveStep,

    -- * Demos
    xsIn,
    parensIn,
    ambIn,
    sexpIn,
    someStuff,
  )
where

import Data.Bool (Bool)
import Data.Eq (Eq)
import Data.Function (($))
import Data.Functor ((<$>))
import Data.Int (Int)
import Data.List (intersperse, replicate, words)
import Data.Ord (Ord)
import Data.Semigroup (Semigroup ((<>)))
import Data.Set (Set)
import Data.String (String)
import Text.Show (Show)
import Prelude (Num ((-)))

-- | Represents both a formal context-free language and the
--   reduction of a member of that language to a value of type @a@.

--   Languages range of `Token' values.

data Parser t a = Parser
  { parserRec :: ParserRec Parser t a,
    parserNullable :: FPValue Bool,
    parserEmpty :: FPValue Bool,
    parserDerive :: Token t -> Parser t a,
    parserCompact :: Parser t a
  }

data ParserRec p t a where
  Alt :: (Ord t, Ord a) => p t a -> p t a -> ParserRec p t a
  Con :: (Ord t, Ord a, Ord b) => p t a -> p t b -> ParserRec p t (a, b)
  Red :: (Ord t, Ord a, Ord b) => (Set a -> Set b) -> p t a -> ParserRec p t b
  Nul :: (Ord t, Ord a) => p t a -> ParserRec p t a
  Zip :: (Ord t, Ord a, Ord b) => p t a -> ContextR p t a b -> ParserRec p t b
  Ter :: (Ord t) => Set t -> ParserRec p t String
  Eps :: (Ord t, Ord a) => Set a -> ParserRec p t a
  Emp :: (Ord t, Ord a) => ParserRec p t a

data ContextR p t a b where
  ConContext ::
    (Ord t, Ord a, Ord b) => p t b -> ContextR p t (a, b) c -> ContextR p t a c
  RedContext ::
    (Ord t, Ord a, Ord b) =>
    (Set a -> Set b) ->
    ContextR p t b c ->
    ContextR p t a c
  TopContext :: (Ord t, Ord a) => ContextR p t a a

data Token t = Token {tokenClass :: t, tokenValue :: String}
  deriving stock (Eq, Ord, Show)

-- | The main derivative function.
derive :: Parser t a -> Token t -> Parser t a
derive = parserDerive

-- | The optimization step of the algorithm.
compact :: Parser t a -> Parser t a
compact = parserCompact

-- running parsers

-- | A specified number of compactions.
compactNum :: Int -> Parser t a -> Parser t a
compactNum 0 p = p
compactNum n p = compactNum (n - 1) (compact p)

-- | Derivation followed by a specified number of compactions.
deriveStepNum :: Int -> Parser t a -> Token t -> Parser t a
deriveStepNum n p i = compactNum n $ derive p i

-- | The number of compact steps that usually keeps a parser constant in size
--   while parsing.
defaultCompactSteps :: Int
defaultCompactSteps = 10

-- | Derivation followed by the default number of compactions.
deriveStep :: Parser t a -> Token t -> Parser t a
deriveStep = deriveStepNum defaultCompactSteps

-- inspecting parsers

data ParserRecType
  = ConType
  | AltType
  | RedType
  | NulType
  | ZipType
  | TerType
  | EpsType
  | EmpType
  deriving stock (Eq, Ord, Show)

-- FPValue

data FPValue a = FPDecided a | FPUndecided
  deriving stock (Eq, Ord, Show)

-- demos

xsIn :: [Token String]
xsIn = replicate 60 (Token "x" "x")

parensIn :: [Token String]
parensIn = replicate 80 (Token "(" "(") <> replicate 80 (Token ")" ")")

ambIn :: [Token String]
ambIn = intersperse (Token "+" "+") (replicate 7 (Token "1" "1"))

sexpIn :: [Token String]
sexpIn =
  (\x -> Token x x)
    <$> words
      "( s ( s ( s s ( s s s ( s s s ( s ) ( s s ) s s ) s s ) s ) s ) )"

-- makeSExpIn :: Int -> [Token String]
-- makeSExpIn n = (\x -> Token x x) <$> words ("( " <> build n "s" <> " )")
--   where
--     build 0 x = x
--     build n s = build (n - 1) s'
--       where
--         s' = "s ( " <> s <> " )"

someStuff :: [Token String]
someStuff = (\x -> Token x x) <$> words "x x x x y y y x x"

-- exprIn :: Int -> [String]
-- exprIn n =
--   foldr (.) id
--         (replicate n (\s -> ("x" :) . ("[" :) . s . ("]" :)))
--         ("x" :)
--         []

-- exprIn2 :: [String]
-- exprIn2 = words "x [ x ] [ x ]"

-- lexing

-- longestFirstMatch :: [(Int, Set a, [Token t])] -> Maybe (a, [Token t])
-- longestFirstMatch rs = fextract <$> foldl pick Nothing rs
--   where
--     pick Nothing s = Just s
--     pick tM@(Just (tlen, _, _)) c@(clen, _, _) | clen > tlen = Just c
--                                                | True   = tM
--     extract (_, res, con) = (Set.toList res !! 0, con)

-- charToken :: Char -> Token Char
-- charToken c = Token c [c]
