module Spec where

import Criterion.Main (bench, defaultMain, nfIO)
import Evaluator (run)
import System.Directory (listDirectory)

main :: IO ()
main = do
  let dir = "input/bench/"
  files <- listDirectory dir
  defaultMain [bench file $ nfIO (run (dir ++ file)) | file <- files]
