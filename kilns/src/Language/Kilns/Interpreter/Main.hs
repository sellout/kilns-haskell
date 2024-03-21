{-# LANGUAGE Unsafe #-}

module Main (main) where

import safe Control.Category ((.))
import safe Control.Monad ((=<<))
import safe Data.Function (($))
import safe Data.Functor (Functor (fmap))
import safe Data.List (unlines)
import safe Data.Maybe (maybe)
import safe Data.Set (Set)
import safe qualified Data.Set as Set
import safe Data.String (String)
import safe Language.KellCalculus.AST (Pattern (grammar), Process)
import Language.KellCalculus.FraKtal (FraKtal)
import Language.KellCalculus.Parser (SexpSyntax (SexpSyntax), processes)
import safe Language.KellCalculus.ReductionSemantics (reduce)
import safe System.Environment (getArgs)
import safe System.IO (IO, print, putStrLn, readFile)
import safe Text.Derp (Token (Token))
import Text.Derp.Unsafe (runParse)

usage :: String
usage =
  unlines
    [ "usage: kilns <file>",
      "",
      "Interpreter for the Kilns programming language.",
      "",
      "Reduces <file> to normal form. If no <file> is provided, shows this usage",
      "message."
    ]

-- syntax :: Show a => a -> a
-- syntax = id
syntax :: a -> SexpSyntax a
syntax = SexpSyntax

parse :: String -> Set (Process FraKtal)
parse = runParse (processes grammar) . fmap (\x -> Token x [x])

reduceFully :: (Pattern ξ) => Process ξ -> Process ξ
reduceFully p = maybe p reduceFully $ reduce p

main :: IO ()
main =
  ( \case
      [file] -> print . Set.map (syntax . reduceFully) . parse =<< readFile file
      _ -> putStrLn usage
  )
    =<< getArgs
