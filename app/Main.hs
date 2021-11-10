module Main where

import Control.Monad (void)
import GCLParser.Parser (parseGCLfile)
import System.Environment (getArgs)
import Verifier (verifyProgram)

parseArgs :: [[Char]] -> (Int, [Char], Bool, Bool)
parseArgs [] = (10, "test/input/reverse.gcl", False, False)
parseArgs ("-K" : arg : args) = (read arg, a2, a3, a4)
  where
    (_, a2, a3, a4) = parseArgs args
parseArgs ("-file" : arg : args) = (a1, arg, a3, a4)
  where
    (a1, _, a3, a4) = parseArgs args
parseArgs ("-wlp" : args) = (a1, a2, True, a4)
  where
    (a1, a2, _, a4) = parseArgs args
parseArgs ("-path" : args) = (a1, a2, a3, True)
  where
    (a1, a2, a3, _) = parseArgs args
parseArgs (arg : args) = parseArgs args

-- loads the file and puts the ParseResult Program through the functions in Verifier
main :: IO ()
main = do
  args <- getArgs
  let parsedArgs@(_, file, _, _) = parseArgs args
  program <- parseGCLfile file
  void (verifyProgram program parsedArgs)
