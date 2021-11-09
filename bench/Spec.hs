module Main where

import Control.Monad (void)
import Criterion.Main (bench, defaultMain, nfIO)
import GCLParser.GCLDatatype
import GCLParser.Parser (parseGCLfile)
import System.Directory (listDirectory)
import System.IO.Unsafe (unsafePerformIO)
import Verifier (verifyProgram)
import Z3.Monad (Result (..))

modProgram :: Either a Program -> Int -> Either a Program
modProgram (Left e) n = Left e
modProgram (Right (Program name input output stmt)) n = do
  let inp = VarDeclaration "N" (PType PTInt)
  let seq = Seq (Assign "N" (LitI n)) stmt
  Right (Program name (inp : input) output seq)

run :: [Char] -> Int -> Int -> IO ()
run file k n = do
  program <- parseGCLfile file
  void (verifyProgram (modProgram program n) (k + 1, file, False, False))

main :: IO ()
main = do
  let dir = "bench/input/"
  files <- listDirectory dir
  let fks = zip files [4, 10, 10]
  defaultMain [bench (f ++ " for N = " ++ show n) $ nfIO (run (dir ++ f) k n) | (f, k) <- fks, n <- [2 .. 10]]

-- findk :: [Char] -> Int -> Int
-- findk file n = head [k | k <- [1 ..], Unsat == unsafePerformIO (verifyProgram (modProgram (unsafePerformIO (parseGCLfile file)) n) (k + 1, file, False, False))]

-- main :: IO ()
-- main = do
--   let dir = "bench/input/"
--   files <- listDirectory dir
--   print [(f, maximum [findk (dir ++ f) n | n <- [2 .. 10]]) | f <- files]
