module Main where

import Criterion.Main (bench, defaultMain, nfIO)
import GCLParser.GCLDatatype
import GCLParser.Parser (parseGCLfile)
import System.Directory (listDirectory)
import Verifier (arguments, verifyProgram)

modProgram :: Either a Program -> Int -> Either a Program
modProgram (Left program) n = Left program
modProgram (Right (Program name input output stmt)) n = do
  let inp = VarDeclaration "" (PType PTInt)
  let seq = Seq (Assign "N" (LitI n)) stmt
  Right (Program name (inp : input) output seq)

run :: [Char] -> IO ()
run file = do
  program <- parseGCLfile file
  -- N = 2 and K = 10
  -- TODO: ForAll N in [2..10] use deep enough K
  verifyProgram (modProgram program 2) (10, file, False, False)

main :: IO ()
main = do
  let dir = "bench/input/"
  files <- listDirectory dir
  defaultMain [bench file $ nfIO (run (dir ++ file)) | file <- files]
