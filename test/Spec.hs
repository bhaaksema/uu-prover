module Main where

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

_findk :: FilePath -> Int -> Int -> Result
_findk file n k = unsafePerformIO (verifyProgram (modProgram (unsafePerformIO (parseGCLfile file)) n) (k + 1, file, False, False, True, True))

findk :: FilePath -> Int -> Int
findk file n = head [if Unsat == _findk file n k then k else head [] | k <- [1 ..], Undef /= _findk file n k]

main :: IO ()
main = do
  let dir = "input/bench/"
  files <- listDirectory dir
  print [(f, maximum [findk (dir ++ f) n | n <- [2 .. 10]]) | f <- files]
