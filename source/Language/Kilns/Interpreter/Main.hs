module Main
    (main) where

import Data.Set (Set)
import System.Environment

import Text.Derp

import Language.KellCalculus.AST
import Language.KellCalculus.FraKtal
import Language.KellCalculus.Parser

parse :: String -> Set (Process FraKtal)
parse s = runParse (process grammar)
          (map (\x -> Token x [x]) ("(par " ++ s ++ "\n)"))

main :: IO ()
main = getArgs >>= readFile . (flip (!!) 0) >>= print . parse 