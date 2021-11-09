module Main where

import Control.Monad (void)
import GCLParser.Parser (parseGCLfile)
import System.Environment (getArgs)
import Verifier (verifyProgram)

-- The following functions will run the 'main' program and output the required information
-- main loads the file and puts the ParseResult Program through the following functions
arguments :: [[Char]] -> (Int, [Char], Bool, Bool)
arguments [] = (10, "test/input/reverse.gcl", False, False)
arguments ("-K" : arg : xs) = (read arg, a2, a3, a4)
  where
    (_, a2, a3, a4) = arguments xs
arguments ("-file" : arg : xs) = (a1, arg, a3, a4)
  where
    (a1, _, a3, a4) = arguments xs
arguments ("-wlp" : xs) = (a1, a2, True, a4)
  where
    (a1, a2, _, a4) = arguments xs
arguments ("-path" : xs) = (a1, a2, a3, True)
  where
    (a1, a2, a3, _) = arguments xs
arguments (x : xs) = arguments xs

main :: IO ()
main = do
  args <- getArgs
  let parsedArgs@(_, file, _, _) = arguments args
  program <- parseGCLfile file
  void (verifyProgram program parsedArgs)
