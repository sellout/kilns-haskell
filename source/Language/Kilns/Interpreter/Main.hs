{-#
  LANGUAGE
  UnicodeSyntax
  #-}

module Main
    (main) where

import Data.Set (Set)
import qualified Data.Set as Set
import System.Environment

import Text.Derp

import Language.KellCalculus.AST
import Language.KellCalculus.FraKtal
import Language.KellCalculus.Parser
import Language.KellCalculus.ReductionSemantics

parse :: String -> Set (Process FraKtal)
parse s = runParse (process grammar)
          (map (\x -> Token x [x]) ("(par " ++ s ++ "\n)"))

reduceFully :: Pattern ξ ⇒ Process ξ → Process ξ
reduceFully p = case reduce p of
                  Just p' -> reduceFully p'
                  Nothing -> p
 
main :: IO ()
main = getArgs
       >>= readFile . (flip (!!) 0)
       >>= print . Set.map reduceFully . parse
