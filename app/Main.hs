module Main where

import Lib
import POC (run)

main :: IO ()
main = do
  r <- run
  print r
