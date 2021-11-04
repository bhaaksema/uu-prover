module Main where

import Criterion.Main (bench, defaultMain, nfIO)
import GCLParser.GCLDatatype
import GCLParser.Parser (parseGCLfile)
import System.Directory (listDirectory)
import Verifier (verifyProgram)

modProgram :: Either a Program -> Int -> Either a Program
modProgram (Left error) n = Left error
modProgram (Right (Program name input output stmt)) n = do
  let inp = VarDeclaration "N" (PType PTInt)
  let seq = Seq (Assign "N" (LitI n)) stmt
  Right (Program name (inp : input) output seq)

run :: [Char] -> Int -> IO ()
run file n = do
  program <- parseGCLfile file
  -- TODO: use deep enough K (is now always 10)
  let k = 10
  verifyProgram (modProgram program n) (k + 1, file, False, False)

main :: IO ()
main = do
  let dir = "bench/input/"
  files <- listDirectory dir
  defaultMain [bench (file ++ " for N = " ++ show n) $ nfIO (run (dir ++ file) n) | file <- files, n <- [2 .. 10]]
