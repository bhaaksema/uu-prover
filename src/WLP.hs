module WLP where

import Data.Bifunctor (Bifunctor (first))
import Data.Map (Map, adjust, empty, fromList, insert, member, toList, (!))
import GCLParser.GCLDatatype
import Z3.Monad

type WLPType = Map String Expr -> (Expr, Map String Expr)

type PostCondition = WLPType

type PostConditions = (WLPType, WLPType)

changeIf :: Expr -> Expr -> Expr -> Expr
changeIf cond trueValue falseValue = NewStore (RepBy cond trueValue falseValue)

updateExc cond trueValue vars = insert "exc" (changeIf (BinopExpr And cond excZero) trueValue (vars ! "exc")) vars
  where
    excZero = BinopExpr Equal (vars ! "exc") (LitI 0)

safeExpression :: Expr -> PostCondition -> Map String Expr -> (Expr, Map String Expr)
safeExpression i@(LitI _) q vars = (i, vars)
safeExpression b@(LitB _) q vars = (b, vars)
safeExpression (BinopExpr Divide expr1 expr2) q vars = do
  let (e1, e1Vars) = safeExpression expr1 q vars
  let (e2, e2Vars) = safeExpression expr2 q e1Vars
  let newVars = updateExc (BinopExpr Equal e2 (LitI 0)) (LitI 1) e2Vars
  (BinopExpr Divide expr1 expr2, newVars)
safeExpression (BinopExpr binop expr1 expr2) q vars = do
  let (e1, e1Vars) = safeExpression expr1 q vars
  let (e2, e2Vars) = safeExpression expr2 q e1Vars
  (BinopExpr binop expr1 expr2, e2Vars)
safeExpression (OpNeg expr) q vars = first OpNeg $ safeExpression expr q vars
safeExpression (Var name) q vars = (vars ! name, vars)
safeExpression (ArrayElem (Var name) index) q vars = (ArrayElem (vars ! name) (considerExpr index vars), vars)
  where
    (_, newVars) = safeExpression index q vars
    lowerBound = BinopExpr LessThan index (LitI 0)
    upperBound = BinopExpr GreaterThanEqual index (Var $ "#" ++ name)
    indexUnsafe = BinopExpr Or lowerBound upperBound
    newVars' = updateExc indexUnsafe (LitI 2) newVars
safeExpression a@(ArrayElem (RepBy e _ _) index) q vars = first (const a) $ safeExpression (ArrayElem e index) q vars -- Evaluate as if there isn't a RepBy, then put it in the first element of the tuple (gives the correct var values)
safeExpression (Parens e) q vars = safeExpression e q vars
safeExpression (SizeOf (Var name)) q vars = (vars ! ("#" ++ name), vars)
safeExpression (Forall locvarName expr) q vars = first (Forall locvarName) $ safeExpression expr q vars
safeExpression (Exists locvarName expr) q vars = first (Exists locvarName) $ safeExpression expr q vars
safeExpression e@NewStore {} q vars = (e, vars) -- This is a wrapper for an if-then-else, thus we just pass the value along
safeExpression e _ _ = error ("Cannot determinte if expression would result in exception: '" ++ show e ++ "'")

wlp :: Stmt -> PostConditions -> WLPType
wlp (Assert expr) (q, r) vars = first (BinopExpr And safe) (q safeVars)
  where
    (safe, safeVars) = safeExpression (considerExpr expr vars) q vars
wlp (Assume expr) (q, r) vars = first (BinopExpr Implication (Parens safe) . Parens) (q safeVars)
  where
    (safe, safeVars) = safeExpression (considerExpr expr vars) q vars
wlp Skip (q, r) vars = q vars
wlp (Seq stmt1 stmt2) (q, r) vars = do
  let stmt2Q = wlp stmt2 (q, r)
  let stmt1Q = wlp stmt1 (stmt2Q, r)
  stmt1Q vars
wlp (Assign name expr) (q, r) vars = do
  let q' = if name == "exc" then r else q
  let (value, safeVars) = safeExpression (considerExpr expr vars) q vars
  let isArray = member ("#" ++ name) vars
  let basicUpdate = insert name value safeVars -- Update the value of this variable to the expression
  let qIfPrimitive = q' basicUpdate --If this is a primitive, evaluate q using the basic map
  let arrayLengthUpdate = insert ("#" ++ name) (safeVars ! ("#" ++ getArrayName expr)) basicUpdate
  let qIfArray = q' arrayLengthUpdate --If this is an array, also update the array length of this variable. Then evaluate q using the new map.
  if isArray then qIfArray else qIfPrimitive
  where
    getArrayName (Var name) = name -- Get name of the variable
    getArrayName (RepBy expr _ _) = getArrayName expr -- Unwrap RepBy to get the name of the original array (we need it to find the length variable later on)
    getArrayName expr = error "Trying to get array name from variable that is not an array: " ++ show expr
wlp (AAssign name indexE expr) (q, r) vars = do
  let array = vars ! name
  let (value, safeVars) = safeExpression (considerExpr expr vars) q vars
  let index = considerExpr indexE vars
  let newVars' = insert name (RepBy array index value) safeVars
  let lowerBound = BinopExpr LessThan index (LitI 0)
  let upperBound = BinopExpr GreaterThanEqual index (Var $ "#" ++ name)
  let newVars = updateExc (BinopExpr Or lowerBound upperBound) (LitI 2) newVars'
  q newVars
wlp s _ _ = error ("Unknown statement '" ++ show s ++ "'")

-- Returns a list of all variables declared in the program
findLocvars :: Stmt -> [VarDeclaration]
findLocvars (Seq stmt1 stmt2) = findLocvars stmt1 ++ findLocvars stmt2
findLocvars (While _ stmt) = findLocvars stmt
findLocvars (IfThenElse _ stmt1 stmt2) = findLocvars stmt1 ++ findLocvars stmt2
findLocvars (Block vars stmt) = vars ++ findLocvars stmt
findLocvars (TryCatch excName tryBlock catchBlock) = VarDeclaration excName (PType PTInt) : findLocvars tryBlock ++ findLocvars catchBlock
findLocvars _ = []

-- Will evaluate the expression using the given variable environment
considerExpr :: Expr -> Map String Expr -> Expr
considerExpr expr = considerExpr' (simplifyExpr expr)

considerExpr' :: Expr -> Map String Expr -> Expr
considerExpr' i@(LitI _) _ = i
considerExpr' b@(LitB _) _ = b
considerExpr' (BinopExpr Plus (Parens e) (LitI i)) vars = considerExpr' (Parens (BinopExpr Plus e (LitI i))) vars
considerExpr' (BinopExpr binop expr1 expr2) vars = evalBinopExpr $ BinopExpr binop (considerExpr expr1 vars) (considerExpr expr2 vars)
considerExpr' (OpNeg expr) vars = OpNeg (considerExpr expr vars)
considerExpr' (Var name) vars = vars ! name
considerExpr' (ArrayElem (Var name) index) vars = ArrayElem (vars ! name) (considerExpr index vars)
considerExpr' a@(ArrayElem _ _) vars = a
considerExpr' (Parens e) vars = considerExpr e vars
considerExpr' (SizeOf (Var name)) vars = vars ! ("#" ++ name)
considerExpr' (Forall locvarName expr) vars = Forall locvarName (considerExpr expr boundedVars)
  where
    boundedVars = insert locvarName (Var locvarName) vars
considerExpr' (Exists locvarName expr) vars = Exists locvarName (considerExpr expr boundedVars)
  where
    boundedVars = insert locvarName (Var locvarName) vars
considerExpr' e@NewStore {} _ = e -- This is a wrapper for an if-then-else, thus we just pass the value along
considerExpr' e _ = error ("Unknown expression '" ++ show e ++ "'")

traceVarExpr :: Stmt -> Map String Expr -> Map String Expr
traceVarExpr (Seq stmt1 stmt2) vars = do
  let vars1 = traceVarExpr stmt1 vars -- Variables after statement 1
  let vars2 = traceVarExpr stmt2 vars1 -- Variables after statement 2
  vars2
traceVarExpr (Assign name expr) vars = do
  let value = considerExpr expr vars
  insert name value vars
traceVarExpr (AAssign name indexE expr) vars = do
  let array = vars ! name
  let value = considerExpr expr vars
  let index = considerExpr indexE vars
  insert name (RepBy array index value) vars
traceVarExpr _ vars = vars

-- Runs the given expression and environment map through Z3
verifyExpr :: Expr -> Map String Type -> IO Result
verifyExpr expr vars = evalZ3 $ do
  assert =<< evalExpr expr (convertVarMap vars)
  check

-- Turns an expression environment from GCL variables to Z3 variables
convertVarMap :: MonadZ3 z3 => Map String Type -> Map String (z3 AST)
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
-- This is a special construct that allows for making a value dependent on a condition. This allows for e.g. exc := IF a == b THEN 0 ELSE 5.
-- This is used especially for the finding the final values of variables.
evalExpr' (NewStore (RepBy condition trueValue falseValue)) vars = do
  ifTrue <- evalExpr trueValue vars
  ifFalse <- evalExpr falseValue vars
  condition <- evalExpr condition vars
  mkIte condition ifTrue ifFalse
evalExpr' e _ = error ("Unknown z3 expression '" ++ show e ++ "'")

evalBinopExpr :: Expr -> Expr
evalBinopExpr (BinopExpr Plus (LitI i1) (LitI i2)) = LitI (i1 + i2)
evalBinopExpr (BinopExpr Minus (LitI i1) (LitI i2)) = LitI (i1 - i2)
evalBinopExpr (BinopExpr Multiply (LitI i1) (LitI i2)) = LitI (i1 * i2)
evalBinopExpr e = e

-- Calculates how many atoms the given expression has
numExprAtoms :: Expr -> Int
numExprAtoms (BinopExpr _ e1 e2) = numExprAtoms e1 + numExprAtoms e2
numExprAtoms (Parens e) = numExprAtoms e
numExprAtoms _ = 1

simplifyExpr :: Expr -> Expr
-- simplifyExpr e = e --Uncomment to disable expression simplification
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
