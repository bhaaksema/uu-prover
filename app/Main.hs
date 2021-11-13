module Main where

import Control.Monad (void)
import GCLParser.Parser (parseGCLfile)
import System.Environment (getArgs)
import Verifier (verifyProgram)

parseArgs :: [[Char]] -> (Int, [Char], Bool, Bool, Bool, Bool)
parseArgs [] = (10, "input/test/reverse.gcl", False, False, True, False)
parseArgs ("-K" : arg : args) = (read arg, a2, a3, a4, a5, a6)
  where
    (_, a2, a3, a4, a5, a6) = parseArgs args
parseArgs ("-file" : arg : args) = (a1, arg, a3, a4, a5, a6)
  where
    (a1, _, a3, a4, a5, a6) = parseArgs args
parseArgs ("-wlp" : args) = (a1, a2, True, a4, a5, a6)
  where
    (a1, a2, _, a4, a5, a6) = parseArgs args
parseArgs ("-path" : args) = (a1, a2, a3, True, a5, a6)
  where
    (a1, a2, a3, _, a5, a6) = parseArgs args
parseArgs ("-Hoff" : args) = (a1, a2, a3, a4, False, a6)
  where
    (a1, a2, a3, a4, _, a6) = parseArgs args
parseArgs ("-noExc" : args) = (a1, a2, a3, a4, a5, True)
  where
    (a1, a2, a3, a4, a5, _) = parseArgs args
parseArgs (arg : args) = parseArgs args

-- loads the file and puts the ParseResult Program through the functions in Verifier
main :: IO ()
main = do
  args <- getArgs
  let parsedArgs@(_, file, _, _, _, _) = parseArgs args
  program <- parseGCLfile file
  void (verifyProgram program parsedArgs)
