module Main where

import System.Environment
import DIMACS
import ReadCNF
import Solver (satisfiable)
import Text.Parsec.String (parseFromFile)

main :: IO ()
main = do {
          args <- getArgs;
          dimacs <- parseFromFile parseDIMACS (args !! 0);
          case dimacs of
            Left err -> print err
            Right xs -> print $ satisfiable xs
            }
