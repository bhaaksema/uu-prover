module Main where

import Criterion.Main (bench, defaultMain, nfIO)
import ProgramPath (run)
import System.Directory (listDirectory)

main :: IO ()
main = do
  files <- listDirectory "input/test/"
  defaultMain [bench file $ nfIO (run ("input/test/" ++ file)) | file <- files]
