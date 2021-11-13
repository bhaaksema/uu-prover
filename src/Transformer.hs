module Transformer where

import Data.Map (Map, fromList, insert, toList, (!))
import ExpressionOps (simplifyExpr)
import GCLParser.GCLDatatype
import GeneralTypes (VarTypes, Z3Vars)
import Z3.Monad

--
-- These functions are for transforming expressions to Z3 ASTs
--

-- Runs the given expression and environment map through Z3
verifyExpr :: Expr -> VarTypes -> IO Result
verifyExpr expr vars = evalZ3 $ do
  assert =<< evalExpr expr (convertVarMap vars)
  check

-- Simplifies the given expression, then transforms it into a Z3 AST
evalExpr :: Expr -> Z3Vars -> Z3 AST
evalExpr expr = evalExpr' (simplifyExpr expr)

-- Transforms the given expression into a Z3 AST, using the given variable map
evalExpr' :: Expr -> Z3Vars -> Z3 AST
evalExpr' (LitI i) _ = do
  sort <- mkIntSort
  mkInt i sort
evalExpr' (LitB b) _ = mkBool b
evalExpr' (BinopExpr binop expr1 expr2) vars = do
  ast1 <- evalExpr expr1 vars
  ast2 <- evalExpr expr2 vars
  evalBinop binop ast1 ast2
evalExpr' (OpNeg expr) vars = do
  ast <- evalExpr expr vars
  mkNot ast
evalExpr' (Var name) vars = vars ! name
evalExpr' (Parens e) vars = evalExpr e vars
evalExpr' (SizeOf (Var name)) vars = vars ! ("#" ++ name)
evalExpr' (ArrayElem a index) vars = do
  index <- evalExpr index vars
  array <- evalExpr a vars
  mkSelect array index
evalExpr' (RepBy arrayInEnv index newValue) vars = do
  value <- evalExpr newValue vars
  index <- evalExpr index vars
  array <- evalExpr arrayInEnv vars
  mkStore array index value
evalExpr' (Forall locvarName expr) vars = do
  iSort <- mkIntSort
  sym <- mkStringSymbol ("!" ++ locvarName)
  let quantifier = mkIntVar sym
  q <- quantifier
  quantifier' <- toApp q
  let boundedVars = insert locvarName quantifier vars
  mkForallConst [] [quantifier'] =<< evalExpr' expr boundedVars
evalExpr' (Exists locvarName expr) vars = do
  iSort <- mkIntSort
  sym <- mkStringSymbol ("!" ++ locvarName)
  let quantifier = mkIntVar sym
  q <- quantifier
  quantifier' <- toApp q
  let boundedVars = insert locvarName quantifier vars
  mkExistsConst [] [quantifier'] =<< evalExpr' expr boundedVars
-- This is a special construct that allows for making a value dependent on a condition. This allows for e.g. exc := IF a == b THEN 0 ELSE 5.
-- This is used especially for the finding the final values of variables.
evalExpr' (Cond condition trueValue falseValue) vars = do
  ifTrue <- evalExpr trueValue vars
  ifFalse <- evalExpr falseValue vars
  condition <- evalExpr condition vars
  mkIte condition ifTrue ifFalse
evalExpr' e _ = error ("Unknown z3 expression '" ++ show e ++ "'")

-- Turns an expression environment from GCL variables to Z3 variables
convertVarMap :: VarTypes -> Z3Vars
convertVarMap types = z3Environment
  where
    convert (key, _) = (key, createVariable key (types ! key))
    createVariable name (PType PTInt) = do
      sym <- mkStringSymbol name
      mkIntVar sym
    createVariable name (PType PTBool) = do
      sym <- mkStringSymbol name
      mkBoolVar sym
    createVariable name (AType PTBool) = do
      iSort <- mkIntSort
      bSort <- mkBoolSort
      aSort <- mkArraySort iSort bSort
      sym <- mkStringSymbol name
      mkConst sym aSort
    createVariable name (AType PTInt) = do
      iSort <- mkIntSort
      aSort <- mkArraySort iSort iSort
      sym <- mkStringSymbol name
      mkConst sym aSort
    createVariable _ typ = error ("Cannot create variable of unknown type " ++ show typ)
    z3Environment = fromList (map convert (toList types))

-- Transforms a Binop to the corresponding Z3 AST
evalBinop :: MonadZ3 z3 => BinOp -> AST -> AST -> z3 AST
evalBinop And ast1 ast2 = mkAnd [ast1, ast2]
evalBinop Or ast1 ast2 = mkOr [ast1, ast2]
evalBinop Implication ast1 ast2 = mkImplies ast1 ast2
evalBinop LessThan ast1 ast2 = mkLt ast1 ast2
evalBinop LessThanEqual ast1 ast2 = mkLe ast1 ast2
evalBinop GreaterThan ast1 ast2 = mkGt ast1 ast2
evalBinop GreaterThanEqual ast1 ast2 = mkGe ast1 ast2
evalBinop Equal ast1 ast2 = mkEq ast1 ast2
evalBinop Minus ast1 ast2 = mkSub [ast1, ast2]
evalBinop Plus ast1 ast2 = mkAdd [ast1, ast2]
evalBinop Multiply ast1 ast2 = mkMul [ast1, ast2]
evalBinop Divide ast1 ast2 = mkDiv ast1 ast2
evalBinop Alias _ _ = mkTrue
