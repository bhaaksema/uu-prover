module Main where

import GCLParser.GCLDatatype
import GCLParser.Parser (parseGCLfile)
import MuGCL (mutateProgram)
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
_findk file n k =
  unsafePerformIO
    ( verifyProgram
        (modProgram (unsafePerformIO (parseGCLfile file)) n)
        (k + 1, file, False, False, True, False)
    )

findk :: FilePath -> Int -> Int
findk file n =
  head
    [ if Unsat == _findk file n k
        then k
        else head []
      | k <- [1 ..],
        Undef /= _findk file n k
    ]

main :: IO ()
main = do
  let dir = "input/bench/"
  files <- listDirectory dir
  print [(f, maximum [findk (dir ++ f) n | n <- [2 .. 10]]) | f <- files]

_kill :: FilePath -> Either a Program -> Int -> Int -> (Int, Int)
_kill _ (Left program) _ _ = (0, 0)
_kill file (Right program) n k =
  ( sum
      [ 1
        | (_, program) <- mutations,
          Unsat
            == unsafePerformIO
              ( verifyProgram
                  (modProgram (Right program) n)
                  (k + 1, file, False, False, True, False)
              )
      ],
    length mutations
  )
  where
    mutations = mutateProgram program

kill :: FilePath -> Int -> Int -> IO (Int, Int)
kill file n k = do
  program <- parseGCLfile file
  return (_kill file program n k)

-- This main function collects the mutation kill statistics, it cannot replace the old main
-- right now because this one results in a Z3 error for a mutatant of bsort.gcl

-- main :: IO ()
-- main = do
--   let dir = "input/bench/"
--   files <- listDirectory dir
--   let fkns = [(f, [(findk (dir ++ f) n, n) | n <- [2 .. 10]]) | f <- files]
--   print [(f, [unsafePerformIO (kill (dir ++ f) n k) | (k, n) <- kns]) | (f, kns) <- fkns]
