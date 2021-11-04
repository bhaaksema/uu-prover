module Main where

import GCLParser.Parser (parseGCLfile)
import System.Directory (listDirectory)
import Verifier (arguments, verifyProgram)

run :: [Char] -> IO ()
run file = do
  let parsedArgs = (10, file, False, False)
  program <- parseGCLfile file
  verifyProgram program parsedArgs

main :: IO ()
main = do
  let dir = "test/input/"
  files <- listDirectory dir
  foldr (>>) (print "") [run (dir ++ file) | file <- files]
