module Main where

import Criterion.Main (bench, defaultMain, nfIO)
import ProgramPath (run)
import System.Directory (listDirectory)

main :: IO ()
main = do
  files <- listDirectory "input/bench/"
  defaultMain [bench file $ nfIO (run ("input/bench/" ++ file)) | file <- files]
