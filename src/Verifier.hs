module Verifier where

import Control.Monad (when)
import Data.Map (empty)
import Evaluator (addExprVariable, calcWLP, evaluateTreeConds, verifyExpr)
import GCLParser.GCLDatatype
import GCLParser.Parser (parseGCLfile)
import ProgramPath
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import Text.Printf (printf)
import WLP (convertVarMap, findLocvars, numExprAtoms)
import Z3.Monad (Result (..), astToString, evalZ3)

-- The following functions will run the 'main' program and output the required information
-- main loads the file and puts the ParseResult Program through the following functions
arguments :: [[Char]] -> (Int, [Char], Bool, Bool)
arguments [] = (10, "test/input/reverse.gcl", False, False)
arguments ("-K" : arg : xs) = (read arg, a2, a3, a4)
  where
    (_, a2, a3, a4) = arguments xs
arguments ("-file" : arg : xs) = (a1, arg, a3, a4)
  where
    (a1, _, a3, a4) = arguments xs
arguments ("-wlp" : xs) = (a1, a2, True, a4)
  where
    (a1, a2, _, a4) = arguments xs
arguments ("-path" : xs) = (a1, a2, a3, True)
  where
    (a1, a2, a3, _) = arguments xs
arguments (x : xs) = arguments xs

run :: IO ()
run = do
  args <- getArgs
  let parsedArgs@(_, file, _, _) = arguments args
  program <- parseGCLfile file
  verifyProgram program parsedArgs

-- Will return if all of the statements were correctly verified
mapUntilSat :: ((Expr, ProgramPath Expr) -> (IO Result, ProgramPath Expr, Expr)) -> [(Expr, ProgramPath Expr)] -> IO (Result, ProgramPath Expr, Expr)
mapUntilSat f [] = return (Unsat, EmptyPath (LitB True), LitB True)
mapUntilSat f (x : xs) = do
  let (r, path, wlp) = f x
  result <- r
  case result of
    Sat -> return (Sat, path, wlp)
    Unsat -> mapUntilSat f xs
    Undef -> do
      (others, otherPath, otherWlp) <- mapUntilSat f xs
      case others of
        Sat -> return (Sat, otherPath, otherWlp)
        _ -> return (Undef, path, wlp)

verifyProgram :: Either a Program -> (Int, [Char], Bool, Bool) -> IO ()
verifyProgram (Left _) _ = putStrLn "unable to parse program"
verifyProgram (Right program) (k, file, printWlp, printPath) = do
  putStrLn ("verifying " ++ file ++ " for K = " ++ show k)
  putStrLn []

  -- Start computation time counter
  start <- getCPUTime
  let path = constructPath program
  let locVars = findLocvars (stmt program)
  let flaggedPath = flagInvalid path k
  let pathsTooLong = numInvalid flaggedPath
  let (clearedPath, branches) = removePaths path k

  -- Create a map with all the variables and an initial value of (Var name)
  let (vars, varTypes) = foldl addExprVariable (empty, empty) (input program ++ output program ++ locVars)
  let varmap = convertVarMap varTypes
  condPath <- evaluateTreeConds clearedPath vars varmap
  let cantBranch = numConditionFalse condPath

  -- Calculate the wlp and initial variable values over the tree
  let wlpsInfo = calcWLP condPath vars
  let wlps = map fst wlpsInfo

  -- Print path if the argument -path was specified
  when printPath $ putStrLn "The path is:"
  when printPath $
    putStrLn (printTree condPath k)

  -- Print wlp and z3 script if -wlp was specified
  when printWlp $ putStrLn "The WLPs are:"
  when printWlp $ print wlps

  -- Statistics
  putStrLn ("inspected paths: " ++ show (countBranches condPath))
  putStrLn ("inspected paths: " ++ show branches)
  putStrLn ("Infeasible paths: " ++ show (branches - length wlps))
  putStrLn ("formula size (atoms): " ++ show (sum (map numExprAtoms wlps)) ++ " from " ++ show (length wlps) ++ " wlps")

  -- Print the result of the verification
  putStrLn []
  (final, finalPath, finalWlp) <- mapUntilSat (\(wlp, path) -> (verifyExpr (OpNeg wlp) (varmap, varTypes), path, wlp)) wlpsInfo
  case final of
    Unsat -> putStrLn "accept (could not find any counterexamples)"
    Undef -> putStrLn "undef (at least one path returned undef, but could not find any counteraxamples)"
    Sat -> do
      putStrLn ("reject (counterexample in path: " ++ show finalPath ++ ")")

  -- Stop computation time counter
  end <- getCPUTime
  let diff = fromIntegral (end - start) / (10 ^ 9)
  printf "computation time: %0.3f ms\n" (diff :: Double)
