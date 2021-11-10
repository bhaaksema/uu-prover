module Verifier where

import Control.Monad (when)
import Data.Map (empty, insert)
import Evaluator (addExprVariable, calcWLP, evaluateTreeConds, verifyExpr)
import GCLParser.GCLDatatype
import ProgramPath
import System.CPUTime (getCPUTime)
import Text.Printf (printf)
import WLP (convertVarMap, findLocvars, numExprAtoms)
import Z3.Monad (Result (..), astToString, evalZ3)

-- Will return if all of the statements were correctly verified
mapUntilSat :: ((Expr, [Stmt]) -> (IO Result, [Stmt], Expr)) -> [(Expr, [Stmt])] -> IO (Result, [Stmt], Expr)
mapUntilSat f [] = return (Unsat, [], LitB True)
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

-- Turns an exception code int into a human readable string
exceptionCodeToString :: Int -> String
exceptionCodeToString 0 = "0 (No exceptions)"
exceptionCodeToString 1 = "1 (Division by 0 error)"
exceptionCodeToString 2 = "2 (Tried to read from invalid array index)"
exceptionCodeToString 3 = "3 (Invalid invariant used)"
exceptionCodeToString i = show i ++ " (Unknown exception)"

-- If the program path is a linear path and ends in an explicit exception, print the exception
printIfException :: [Stmt] -> IO ()
printIfException [] = return ()
printIfException statements = when hasError $ putStrLn $ "Unhandled exception: " ++ exceptionCodeToString (getErrorCode (last statements))
  where
    hasError = getErrorCode (last statements) /= 0
    getErrorCode (Assign "exc" (LitI code)) = code
    getErrorCode _ = 0

-- Main funtion that verifies the program
verifyProgram :: Either a Program -> (Int, [Char], Bool, Bool) -> IO Result
verifyProgram (Left _) _ = do
  putStrLn "unable to parse program"
  return Undef
verifyProgram (Right program) (k, file, printWlp, printPath) = do
  putStrLn ("verifying " ++ file ++ " for K = " ++ show k)
  putStrLn []

  -- Start computation time counter
  start <- getCPUTime
  let path = constructPath program
  let locVars = findLocvars (stmt program)
  let (clearedPath, branches) = removePaths path k

  -- Create a map with all the variables and an initial value of (Var name)
  let (vars', varTypes') = foldl addExprVariable (empty, empty) (input program ++ output program ++ locVars)
  -- Add entries for the exception code variable
  let vars = insert "exc" (LitI 0) vars'
  let varTypes = insert "exc" (PType PTInt) varTypes'
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
  putStrLn ("infeasible paths: " ++ show (branches - length wlps))
  putStrLn ("formula size (atoms): " ++ show (sum (map numExprAtoms wlps)) ++ " from " ++ show (length wlps) ++ " wlps")

  -- Print the result of the verification
  putStrLn []
  (final, finalPath, finalWlp) <- mapUntilSat (\(wlp, path) -> (verifyExpr (OpNeg wlp) (varmap, varTypes), path, wlp)) wlpsInfo
  let result = if branches == 0 then Undef else final
  case result of
    Unsat -> putStrLn "accept (could not find any counterexamples)"
    Undef ->
      if branches == 0
        then putStrLn "undef (set of inspected paths is empty)"
        else putStrLn "undef (at least one path returned undef, but could not find any counteraxamples)"
    Sat -> do
      putStrLn ("reject (counterexample in path: " ++ show finalPath ++ ")")
      when printWlp $ putStrLn ("(counterexample in wlp: " ++ show finalWlp ++ ")")
      printIfException finalPath

  -- Stop computation time counter
  end <- getCPUTime
  let diff = fromIntegral (end - start) / (10 ^ 9)
  printf "computation time: %0.3f ms\n" (diff :: Double)
  return result
