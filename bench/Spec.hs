module Main where

import Control.Monad (void)
import Criterion.Main (bench, bgroup, defaultMain, nfIO)
import GCLParser.GCLDatatype
import GCLParser.Parser (parseGCLfile)
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
  void (verifyProgram (modProgram program n) (k + 1, file, False, False, h, True))

main :: IO ()
main = do
  let dir = "input/bench/"
  files <- listDirectory dir
  defaultMain
    [ bgroup
        f
        [ bgroup
            ("N=" ++ show n ++ "/K=" ++ show k)
            [ bench
                ("H=" ++ show h)
                $ nfIO (run (dir ++ f) k n h)
              | h <- [True, False]
            ]
          | (n, k) <- zip [2 .. 10] [8 ..]
        ]
      | f <- files
    ]
