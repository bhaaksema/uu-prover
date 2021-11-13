module Main where

import Control.Monad (void)
import GCLParser.Parser (parseGCLfile)
import System.Directory (listDirectory)
import Verifier (verifyProgram)

run :: Int -> [Char] -> IO ()
run k file = do
  let parsedArgs = (k, file, False, False, True)
  program <- parseGCLfile file
  void (verifyProgram program parsedArgs)

main :: IO ()
main = do
  let dir = "test/input/"
  files <- listDirectory dir
  foldr (>>) (print "") [run k (dir ++ file) | file <- files, k <- [0 .. 20]]
