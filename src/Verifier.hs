module Verifier where

import BranchConditionEvaluator (evaluateTreeConds)
import Control.Monad (when)
import Data.Map (Map, empty, insert)
import Evaluator (addExprVariable, calcWLP, verifyExpr)
import ExpressionOps (numExprAtoms)
import GCLParser.GCLDatatype
import GeneralTypes
import ProgramPath
import System.CPUTime (getCPUTime)
import Text.Printf (printf)
import Transformer (convertVarMap)
import WLP (findLocvars)
import Z3.Monad (Result (..), astToString, evalZ3)

type WLP = (Expr, GCLVars)

type WLPEvaluatingFunction = ((WLP, PathStatements) -> (IO (Result, ExceptionCode), PathStatements, WLP))

type WLPEvaluationResult = IO ((Result, ExceptionCode), PathStatements, WLP)

type WLPList = [(WLP, PathStatements)]

-- Will return if all of the statements were correctly verified
mapUntilSat :: WLPEvaluatingFunction -> WLPList -> WLPEvaluationResult
mapUntilSat f [] = return ((Unsat, 0), [], (LitB True, empty)) -- This means no invalid WLP could be found
mapUntilSat f (x : xs) = do
  let (r, path, wlp) = f x
  (result, exc) <- r
  case result of
    Sat -> return ((Sat, exc), path, wlp)
    Unsat -> mapUntilSat f xs
    Undef -> do
      ((others, otherExc), otherPath, otherWlp) <- mapUntilSat f xs
      case others of
        Sat -> return ((Sat, otherExc), otherPath, otherWlp)
        _ -> return ((Undef, otherExc), path, wlp)

-- Turns an exception code int into a human readable string
exceptionCodeToString :: ExceptionCode -> String
exceptionCodeToString 0 = "0 (No exceptions)"
exceptionCodeToString 1 = "1 (Division by 0 error)"
exceptionCodeToString 2 = "2 (Tried to read from invalid array index)"
exceptionCodeToString 3 = "3 (Invalid invariant used)"
exceptionCodeToString i = show i ++ " (Unknown exception)"

-- If the program path is a linear path and ends in an explicit exception, print the exception
printIfException :: ExceptionCode -> IO ()
printIfException 0 = return ()
printIfException i = putStrLn $ "Unhandled exception: " ++ exceptionCodeToString i

renameSpecials :: Program -> Program
renameSpecials (Program name inputs outputs stmts) = Program name (declRename inputs) (declRename outputs) (renameSpecials' stmts)
  where
    declRename = map (\(VarDeclaration name t) -> if name == "exc" then VarDeclaration "exc'" t else VarDeclaration name t)

    renameSpecials' (Seq stmt1 stmt2) = Seq (renameSpecials' stmt1) (renameSpecials' stmt2)
    renameSpecials' (While guard stmt) = While guard (renameSpecials' stmt)
    renameSpecials' (IfThenElse guard stmt1 stmt2) = IfThenElse guard (renameSpecials' stmt1) (renameSpecials' stmt2)
    renameSpecials' (Block vars stmt) = Block (declRename vars) stmt
    renameSpecials' (TryCatch "exc" tryBlock catchBlock) = renameSpecials' (TryCatch "exc'" tryBlock catchBlock)
    renameSpecials' (TryCatch ename tryBlock catchBlock) = TryCatch ename (renameSpecials' tryBlock) (renameSpecials' catchBlock)
    renameSpecials' s = s

-- Main funtion that verifies the program
verifyProgram :: Either a Program -> (Int, [Char], Bool, Bool) -> IO Result
verifyProgram (Left _) _ = do
  putStrLn "unable to parse program"
  return Undef
verifyProgram (Right program') (k, file, printWlp, printPath) = do
  putStrLn ("verifying " ++ file ++ " for K = " ++ show k)
  putStrLn []

  -- Start computation time counter
  start <- getCPUTime
  let program = renameSpecials program'
  let locVars = findLocvars (stmt program)
  let (clearedPath, branches) = removePaths k . constructPath $ program

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
  let wlps = map (fst . fst) wlpsInfo

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
  ((evalVerdict, excCode), finalPath, (finalWlp, finalVars)) <- mapUntilSat (\((wlp, vars), path) -> (verifyExpr (OpNeg wlp) (varmap, vars, varTypes), path, (wlp, vars))) wlpsInfo
  let result = if branches == 0 then Undef else evalVerdict
  case result of
    Unsat -> putStrLn "accept (could not find any counterexamples)"
    Undef ->
      if branches == 0
        then putStrLn "undef (set of inspected paths is empty)"
        else putStrLn "undef (at least one path returned undef, but could not find any counteraxamples)"
    Sat -> do
      putStrLn ("reject (counterexample in path: " ++ show finalPath ++ ")")
      when printWlp $ putStrLn ("(counterexample in wlp: " ++ show finalWlp ++ ")")
      printIfException excCode

  -- Stop computation time counter
  end <- getCPUTime
  let diff = fromIntegral (end - start) / (10 ^ 9)
  printf "computation time: %0.3f ms\n" (diff :: Double)
  return result
