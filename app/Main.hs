module Main where

import GCLParser.Parser (parseGCLfile)
import ProgramPath (run)
import WLP (verifyProgram)

main :: IO ()
main = run
