module Main where

import Control.Monad (void)
import GCLParser.Parser (parseGCLfile)
import System.Directory (listDirectory)
import Verifier (verifyProgram)

run :: [Char] -> IO ()
run file = do
  let parsedArgs = (10, file, False, False)
  program <- parseGCLfile file
  void (verifyProgram program parsedArgs)

main :: IO ()
main = do
  let dir = "test/input/"
  files <- listDirectory dir
  foldr (>>) (print "") [run (dir ++ file) | file <- files]
