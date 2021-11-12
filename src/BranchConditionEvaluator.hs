{-# LANGUAGE LambdaCase #-}

module BranchConditionEvaluator where

import Data.Map (Map)
import ExpressionOps (considerExpr)
import GCLParser.GCLDatatype (Expr (LitB))
import GeneralTypes (GCLVars, Z3Vars)
import ProgramPath (ProgramPath (AnnotedWhilePath, BranchPath, EmptyPath, InvalidPath, LinearPath, TryCatchPath))
import Transformer (evalExpr)
import WLP (traceVarExpr)
import Z3.Monad (AST, Result (Sat), Z3, assert, check, evalZ3, push, reset)

-- These functions are for the evaluation of branch conditions. This is done as preprocessing, so that the final evaluation does not have to check infeasible

evaluateTreeConds :: ProgramPath Expr -> GCLVars -> Z3Vars -> IO (ProgramPath Expr)
evaluateTreeConds (BranchPath cond stmts option1 option2) vars varmap = do
  let evaluatedCond = considerExpr cond vars
  condExpr <- z3Satisfiable evaluatedCond varmap
  let newVars = maybe vars (`traceVarExpr` vars) stmts
  case condExpr of
    LitB False -> return (BranchPath condExpr stmts option1 option2)
    _ -> do
      newTree1 <- evaluateTreeConds option1 newVars varmap
      newTree2 <- evaluateTreeConds option2 newVars varmap
      return (BranchPath cond stmts newTree1 newTree2)
evaluateTreeConds path@(AnnotedWhilePath invar guard whilePath nextPath) vars varmap = return path -- Note that no path can be evaluated anymore now! There could be many possibilities of variables changing inside of the whilePath if it has a tree inside it.
evaluateTreeConds path@TryCatchPath {} vars varmap = return path -- Note that no path can be evaluated anymore now! There could be many possibilities of variables changing inside of the tryPath if it has an error inside it.
evaluateTreeConds linpath@(LinearPath cond stmts) vars varmap = do
  let evaluatedCond = considerExpr cond vars
  condExpr <- z3Satisfiable evaluatedCond varmap
  case condExpr of
    LitB False -> return $ LinearPath condExpr stmts
    _ -> return $ LinearPath cond stmts
evaluateTreeConds (EmptyPath cond) vars varmap = do
  let evaluatedCond = considerExpr cond vars
  condExpr <- z3Satisfiable evaluatedCond varmap
  condExpr <- z3Satisfiable evaluatedCond varmap
  case condExpr of
    LitB False -> return $ EmptyPath condExpr
    _ -> return $ EmptyPath cond
evaluateTreeConds InvalidPath _ _ = return InvalidPath

-- Checks an expression using a Z3 variable map. If it is not satisfiable will return the LitB expression, else the original expression.
z3Satisfiable :: Expr -> Z3Vars -> IO Expr
z3Satisfiable expr varmap = do
  evalZ3 script >>= \case
    Sat -> return expr
    _ -> return (LitB False)
  where
    script = do
      reset
      push
      assert =<< evalExpr expr varmap
      check
