module WLP where

import Data.Map (Map, adjust, empty, fromList, insert, toList, (!))
import GCLParser.GCLDatatype
import GCLParser.Parser (ParseResult)
import GHC.ResponseFile (expandResponse)
import Z3.Monad

wlp :: Stmt -> Expr -> Map String Expr -> (Expr, Map String Expr)
wlp (Assert expr) q vars = (BinopExpr And (considerExpr expr vars) q, vars)
wlp (Assume expr) q vars = (BinopExpr Implication (Parens (considerExpr expr vars)) (Parens q), vars)
wlp Skip q vars = (q, vars)
wlp (Seq stmt1 stmt2) q vars = do
  let (_, stmt1Vars) = wlp stmt1 (LitB True) vars
  let (stmt2Ast, stmt2Vars) = wlp stmt2 q stmt1Vars
  let (w, _) = wlp stmt1 stmt2Ast vars
  (w, stmt2Vars)
wlp (Assign name expr) q vars = do
  let value = considerExpr expr vars
  (q, insert name value vars)
wlp (AAssign name indexE expr) q vars = do
  let array = vars ! name
  let value = considerExpr expr vars
  let index = considerExpr indexE vars
  (q, insert name (RepBy array index value) vars)
wlp s _ _ = error ("Unknown statement '" ++ show s ++ "'")

--Returns a list of all variables declared in the program
findLocvars :: Stmt -> [VarDeclaration]
findLocvars (Seq stmt1 stmt2) = findLocvars stmt1 ++ findLocvars stmt2
findLocvars (While _ stmt) = findLocvars stmt
findLocvars (IfThenElse _ stmt1 stmt2) = findLocvars stmt1 ++ findLocvars stmt2
findLocvars (Block vars stmt) = vars ++ findLocvars stmt
findLocvars _ = []

-- Will evaluate the expression using the given variable environment
considerExpr :: Expr -> Map String Expr -> Expr
considerExpr expr = considerExpr' (simplifyExpr expr)

considerExpr' :: Expr -> Map String Expr -> Expr
considerExpr' i@(LitI _) _ = i
considerExpr' b@(LitB _) _ = b
considerExpr' (BinopExpr binop expr1 expr2) vars = BinopExpr binop (considerExpr expr1 vars) (considerExpr expr2 vars)
considerExpr' (OpNeg expr) vars = OpNeg (considerExpr expr vars)
considerExpr' (Var name) vars = vars ! name
considerExpr' (ArrayElem (Var name) index) vars = ArrayElem (vars ! name) index
considerExpr' (Parens e) vars = considerExpr e vars
considerExpr' (SizeOf (Var name)) vars = vars ! ("#" ++ name)
considerExpr' (Forall locvarName expr) vars = Forall locvarName (considerExpr expr boundedVars)
  where boundedVars = insert locvarName (Var locvarName) vars
considerExpr' (Exists locvarName expr) vars = Exists locvarName (considerExpr expr boundedVars)
  where boundedVars = insert locvarName (Var locvarName) vars
considerExpr' e _ = error ("Unknown expression '" ++ show e ++ "'")

-- Runs the given expression and environment map through Z3
verifyExpr :: Expr -> (Map String Expr, Map String Type) -> IO Result
verifyExpr expr vars = evalZ3 $ do
  assert =<< evalExpr expr (convertVarMap vars)
  check

-- Turns an expression environment from GCL variables to Z3 variables
convertVarMap :: MonadZ3 z3 => (Map String Expr, Map String Type) -> Map String (z3 AST)
convertVarMap (vars, types) = z3Environment
  where
    convert (key, Var name)
      | key == name = (key, createVariable name (types ! name))
      | otherwise = (key, evalExpr (Var name) z3Environment)
    convert (key, expr)
      | types ! key == AType PTInt = convert (key, Var key)
      | types ! key == AType PTBool = convert (key, Var key)
      | otherwise = (key, evalExpr expr z3Environment)
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
    z3Environment = fromList (map convert (toList vars))

-- TODO: size forall exists var
evalExpr :: MonadZ3 z3 => Expr -> Map String (z3 AST) -> z3 AST
evalExpr expr = evalExpr' (simplifyExpr expr)

evalExpr' :: MonadZ3 z3 => Expr -> Map String (z3 AST) -> z3 AST
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
evalExpr' e _ = error ("Unknown z3 expression '" ++ show e ++ "'")

-- Calculates how many atoms the given expression has
numExprAtoms :: Expr -> Int
numExprAtoms (BinopExpr _ e1 e2) = numExprAtoms e1 + numExprAtoms e2
numExprAtoms (Parens e) = numExprAtoms e
numExprAtoms _ = 1

simplifyExpr :: Expr -> Expr
--simplifyExpr e = e --Uncomment to disable expression simplification
simplifyExpr (BinopExpr And (LitB False) _) = LitB False
simplifyExpr (BinopExpr And _ (LitB False)) = LitB False
simplifyExpr (BinopExpr And (LitB True) (LitB True)) = LitB True
simplifyExpr (BinopExpr And (LitB True) expr) = simplifyExpr expr
simplifyExpr (BinopExpr And expr (LitB True)) = simplifyExpr expr
simplifyExpr (BinopExpr Or (LitB True) _) = LitB True
simplifyExpr (BinopExpr Or _ (LitB True)) = LitB True
simplifyExpr (BinopExpr Or (LitB False) expr) = simplifyExpr expr
simplifyExpr (BinopExpr Or expr (LitB False)) = simplifyExpr expr
simplifyExpr (BinopExpr Implication (LitB True) expr) = simplifyExpr expr
simplifyExpr (BinopExpr op expr1 expr2) = BinopExpr op (simplifyExpr expr1) (simplifyExpr expr2)
simplifyExpr (Parens e) = Parens (simplifyExpr e)
simplifyExpr (OpNeg (LitB False)) = LitB True
simplifyExpr (OpNeg (LitB True)) = LitB False
simplifyExpr expr = expr

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
