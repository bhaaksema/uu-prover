module Main where

import Evaluator (run)
import System.Directory (listDirectory)

main :: IO ()
main = do
  let dir = "input/test/"
  files <- listDirectory dir
  print [run (dir ++ file) | file <- files]
