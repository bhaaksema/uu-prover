module Main where

import Control.Monad (void)
import Criterion.Main (bench, defaultMain, nfIO)
import GCLParser.GCLDatatype
import GCLParser.Parser (parseGCLfile)
import MuGCL (mutateProgram)
import System.Directory (listDirectory)
import Verifier (verifyProgram)

modProgram :: Either a Program -> Int -> Either a Program
modProgram (Left e) n = Left e
modProgram (Right (Program name input output stmt)) n = do
  let inp = VarDeclaration "N" (PType PTInt)
  let seq = Seq (Assign "N" (LitI n)) stmt
  Right (Program name (inp : input) output seq)

run :: [Char] -> Int -> Int -> Bool -> IO ()
run file k n h = do
  program <- parseGCLfile file
  void (verifyProgram (modProgram program n) (k + 1, file, False, False, h))

main :: IO ()
main = do
  let dir = "input/bench/"
  files <- listDirectory dir
  defaultMain [bench (f ++ "{K=" ++ show k ++ ",N=" ++ show n ++ ",H=" ++ show h ++ "}") $ nfIO (run (dir ++ f) k n h) | f <- files, n <- [2 .. 10], h <- [True, False]]
  where
    k = 5
