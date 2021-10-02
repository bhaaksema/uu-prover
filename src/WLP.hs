module WLP where

import GCLParser.GCLDatatype
import GCLParser.Parser (ParseResult)
import GHC.ResponseFile (expandResponse)
import Z3.Monad

verifyProgram :: ParseResult Program -> IO Result
verifyProgram program = evalZ3 $ do
  assert =<< evalProgram program
  check

evalProgram :: MonadZ3 z3 => ParseResult Program -> z3 AST
evalProgram (Right prog) = evalStmt (stmt prog)
evalProgram (Left err) = mkFalse

-- TODO: assign array-assign
evalStmt :: MonadZ3 z3 => Stmt -> z3 AST
evalStmt (Seq Skip stmt) = evalStmt stmt
evalStmt (Seq (Assume expr) stmt) = do
  ast1 <- evalExpr expr
  ast2 <- evalStmt stmt
  mkImplies ast1 ast2
evalStmt (Seq stmt1 stmt2) = do
  ast1 <- evalStmt stmt1
  ast2 <- evalStmt stmt2
  mkAnd [ast1, ast2]
evalStmt (Assert expr) = evalExpr expr
evalStmt _ = mkTrue

-- TODO: size forall exists var
evalExpr :: MonadZ3 z3 => Expr -> z3 AST
evalExpr (LitI i) = do
  sort <- mkIntSort
  mkInt i sort
evalExpr (LitB b) = mkBool b
evalExpr (BinopExpr binop expr1 expr2) = do
  ast1 <- evalExpr expr1
  ast2 <- evalExpr expr2
  evalBinop binop ast1 ast2
evalExpr (OpNeg expr) = do
  ast <- evalExpr expr
  mkNot ast
evalExpr _ = mkTrue

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
