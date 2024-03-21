{-# LANGUAGE Unsafe #-}

module Main (main) where

import safe Control.Category ((.))
import safe Control.Monad ((<=<), (=<<))
import safe Data.Function (flip, ($))
import safe Data.Functor ((<$>))
import safe Data.List ((!!))
import safe Data.Maybe (maybe)
import safe Data.Semigroup ((<>))
import safe Data.Set (Set)
import safe qualified Data.Set as Set
import safe Data.String (String)
import safe Language.KellCalculus.AST (Pattern (grammar), Process)
import Language.KellCalculus.FraKtal (FraKtal)
import Language.KellCalculus.Parser (SexpSyntax (SexpSyntax), process)
import safe Language.KellCalculus.ReductionSemantics (reduce)
import safe System.Environment (getArgs)
import safe System.IO (IO, print, readFile)
import safe Text.Derp (Token (Token))
import Text.Derp.Unsafe (runParse)

-- syntax :: Show a => a -> a
-- syntax = id
syntax :: a -> SexpSyntax a
syntax = SexpSyntax

parse :: String -> Set (Process FraKtal)
parse s =
  runParse (process grammar) $ (\x -> Token x [x]) <$> "(par " <> s <> "\n)"

reduceFully :: (Pattern ξ) => Process ξ -> Process ξ
reduceFully p = maybe p reduceFully $ reduce p

main :: IO ()
main =
  (print . Set.map (syntax . reduceFully) . parse <=< readFile . flip (!!) 0)
    =<< getArgs
