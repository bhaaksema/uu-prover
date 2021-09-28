module Main where

import GCLParser.Parser (parseGCLfile)
import WLP (verifyProgram)

main :: IO ()
main = do
  program <- parseGCLfile "test/input/min.gcl"
  result <- verifyProgram program
  print result
