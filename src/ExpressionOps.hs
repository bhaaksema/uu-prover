module ExpressionOps where

import Data.Bifunctor
import Data.Map
import GCLParser.GCLDatatype
import GeneralTypes

--
-- These functions define simple operations over expressions
--

changeIf :: Expr -> Expr -> Expr -> Expr
changeIf cond trueValue falseValue = NewStore (RepBy cond trueValue falseValue)

updateExc :: Condition -> Expr -> GCLVars -> GCLVars
updateExc cond trueValue vars = insert "exc" (changeIf (BinopExpr And cond excZero) trueValue (vars ! "exc")) vars
  where
    excZero = BinopExpr Equal (vars ! "exc") (LitI 0)

safeExpression :: Expr -> PostCondition -> GCLVars -> (Expr, GCLVars)
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
safeExpression (ArrayElem (Var name) index) q vars = (ArrayElem (vars ! name) safeIndex, newVars)
  where
    (safeIndex, newVars) = safeExpression index q vars
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

-- Will evaluate the expression using the given variable environment
considerExpr :: Expr -> GCLVars -> Expr
considerExpr expr = considerExpr' (simplifyExpr expr)

considerExpr' :: Expr -> GCLVars -> Expr
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