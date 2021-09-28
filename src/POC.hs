module POC where

import GCLParser.GCLDatatype
import GCLParser.Parser (ParseResult, parseGCLfile)
import Z3.Monad

-- main loads the file and puts the ParseResult Program through the following functions
run :: IO Result
run = do
  program <- parseGCLfile "min.gcl"
  checkProgram program

-- Takes a parsed program and returns an IO result
-- This result is Sat, if the assert is satisfiable, or Unsat if it is unsatisfiable
checkProgram :: ParseResult Program -> IO Result
checkProgram program = evalZ3 $ do
  -- evaluate all statements in the program (i.e. calculate wlp over all statements), than add this to the "big assert" of z3
  assert =<< evalProgram program
  check

evalProgram :: MonadZ3 z3 => ParseResult Program -> z3 AST
evalProgram (Left e) = mkFalse --Parse error: let check always fail
evalProgram (Right p) = evalStmt (stmt p) mkTrue --Return wlp over all statements

--evalStmt basically calculates wlp
evalStmt :: MonadZ3 z3 => Stmt -> z3 AST -> z3 AST
evalStmt (Seq a b) q = do
  s1 <- evalStmt a q
  s2 <- evalStmt b q
  mkAnd [s1, s2]
evalStmt (Assert e) q = do
  result <- evalExpr e
  pureQ <- q
  mkAnd [result, pureQ]
evalStmt a _ = mkTrue

-- Turns an expression into an AST
-- Question: Would the Q from evalStmt be necessary here?
evalExpr :: MonadZ3 z3 => Expr -> z3 AST
evalExpr (BinopExpr LessThan e1 e2) = do
  ee1 <- evalExpr e1
  ee2 <- evalExpr e2
  mkLt ee1 ee2
evalExpr (LitI i) = do
  sort <- mkIntSort
  mkInt i sort
evalExpr _ = mkTrue
