module ExpressionOps where

import Data.Bifunctor
import Data.Map
import GCLParser.GCLDatatype
import GeneralTypes

type DefaultValue = Expr

--
-- These functions define simple operations over expressions
--

changeIf :: Condition -> Expr -> DefaultValue -> Expr
changeIf = Cond

updateExc :: Condition -> Expr -> GCLVars -> GCLVars
updateExc cond trueValue vars = insert "exc" (changeIf (BinopExpr And cond excZero) trueValue (vars ! "exc")) vars
  where
    excZero = BinopExpr Equal (vars ! "exc") (LitI 0)

safeExpressionAndPostcondition :: Expr -> PostConditions -> GCLVars -> GCLVars -> (Expr, (Expr, GCLVars), GCLVars)
safeExpressionAndPostcondition expr (q, r) originalVariables postcondVariables = (safeExpr, qrSelector, safeVars)
  where
    (safeExpr, safeVars) = safeExpression expr originalVariables
    newExcValue = safeVars ! "exc"
    postcondVariables' = insert "exc" newExcValue postcondVariables
    (ifQ, qVars) = q postcondVariables'
    (ifR, rVars) = r postcondVariables'
    -- Will select the correct post condition (q or r) depending on what the exc value is
    qrSelector = (changeIf excNotZero ifR ifQ, combinedVars)
    -- Now: Combine qVars and rVars st every value becomes \(qValue,rValue) -> if noError qValue else rValue
    combinedVars = mapWithKey (\name qValue -> changeIf excNotZero (rVars ! name) qValue) qVars
    excNotZero = OpNeg (BinopExpr Equal (safeVars ! "exc") (LitI 0))

safeExpression :: Expr -> GCLVars -> (Expr, GCLVars)
-- The following patterns will be able to change the exc value
safeExpression a@(ArrayElem (Var name) index) vars = (ArrayElem (Var name) safeIndex, newVars')
  where
    (safeIndex, newVars) = safeExpression index vars
    lowerBound = BinopExpr LessThan index (LitI 0)
    upperBound = BinopExpr GreaterThanEqual index (Var $ "#" ++ name)
    indexUnsafe = BinopExpr Or lowerBound upperBound
    newVars' = updateExc indexUnsafe (LitI 2) newVars
safeExpression a@(ArrayElem (RepBy e _ _) index) vars = first (const a) $ safeExpression (ArrayElem e index) vars -- Evaluate as if there isn't a RepBy, then put it in the first element of the tuple (gives the correct var values)
safeExpression (BinopExpr Divide expr1 expr2) vars = do
  let (e1, e1Vars) = safeExpression expr1 vars
  let (e2, e2Vars) = safeExpression expr2 e1Vars
  let e2Zero = BinopExpr Equal e2 (LitI 0)
  let newE2 = changeIf e2Zero (LitI 1) e2 -- Note we just make it not divide by 0 anymore. This is so that Z3 won't crash. Because we also set exc, we internally know there was a division by 0.
  let newVars = updateExc e2Zero (LitI 1) e2Vars
  (BinopExpr Divide e1 newE2, newVars)
-- All these patterns are either safe or check their inner vars
safeExpression i@(LitI _) vars = (i, vars)
safeExpression b@(LitB _) vars = (b, vars)
safeExpression (BinopExpr binop expr1 expr2) vars = do
  let (e1, e1Vars) = safeExpression expr1 vars
  let (e2, e2Vars) = safeExpression expr2 e1Vars
  (BinopExpr binop e1 e2, e2Vars)
safeExpression (OpNeg expr) vars = first OpNeg $ safeExpression expr vars
safeExpression (Var name) vars = (Var name, vars)
safeExpression (Parens e) vars = safeExpression e vars
safeExpression (SizeOf (Var name)) vars = (SizeOf (Var name), vars)
safeExpression q@(Forall locvarName expr) vars = (q, vars) -- Because forall introduces a fresh variable, we are unable to see whether e.g. i in a[i] lies within the correct bounds
safeExpression q@(Exists locvarName expr) vars = (q, vars) -- Same for exists
safeExpression e@Cond {} vars = (e, vars) -- This is a wrapper for an if-then-else, thus we just pass the value along
safeExpression e _ = error ("Cannot determinte if expression would result in exception: '" ++ show e ++ "'")

removeCondExprs :: Expr -> Expr
removeCondExprs (Cond _ _ expr) = removeCondExprs expr
removeCondExprs (BinopExpr b e1 e2) = BinopExpr b (removeCondExprs e1) (removeCondExprs e2)
removeCondExprs (ArrayElem index val) = ArrayElem (removeCondExprs index) (removeCondExprs val)
removeCondExprs (RepBy e1 e2 e3) = RepBy (removeCondExprs e1) (removeCondExprs e2) (removeCondExprs e3)
removeCondExprs (Parens e) = Parens (removeCondExprs e)
removeCondExprs (OpNeg e) = OpNeg (removeCondExprs e)
removeCondExprs (SizeOf e) = SizeOf (removeCondExprs e)
removeCondExprs e = e

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
considerExpr' (Cond c e1 e2) vars = Cond (considerExpr c vars) (considerExpr e1 vars) (considerExpr e2 vars)
considerExpr' e _ = error ("Unknown expression '" ++ show e ++ "'")

evalBinopExpr :: Expr -> Expr
evalBinopExpr e@(BinopExpr Divide _ _) = e -- We cannot do division, we don't know whether we get an integer as result
evalBinopExpr (BinopExpr Plus (LitI i1) (LitI i2)) = LitI (i1 + i2)
evalBinopExpr (BinopExpr Minus (LitI i1) (LitI i2)) = LitI (i1 - i2)
evalBinopExpr (BinopExpr Multiply (LitI i1) (LitI i2)) = LitI (i1 * i2)
-- (i1 + x) + i2 = (i1 + i2) + x
evalBinopExpr (BinopExpr Plus ((BinopExpr Plus (LitI i1) other)) (LitI i2)) = BinopExpr Plus onePlustwo other
  where onePlustwo = LitI (i1 + i2)
-- (x + i1) + i2 = (i1 + i2) + x
evalBinopExpr (BinopExpr Plus ((BinopExpr Plus other (LitI i1))) (LitI i2)) = BinopExpr Plus onePlustwo other
  where onePlustwo = LitI (i1 + i2)
-- (i1 - x) + i2 = (i1 + i2) - x
evalBinopExpr (BinopExpr Plus ((BinopExpr Minus (LitI i1) other)) (LitI i2)) = BinopExpr Minus onePlustwo other
  where onePlustwo = LitI (i1 + i2)
-- (x - i1) + i2 = (i2-i1) + x
evalBinopExpr (BinopExpr Plus ((BinopExpr Minus other (LitI i1))) (LitI i2)) = BinopExpr Plus twoMinusOne other
  where twoMinusOne = LitI (i2 - i1)
-- (y) - i2 = (y) + (-i2)
evalBinopExpr (BinopExpr Minus b (LitI i2)) = evalBinopExpr $ BinopExpr Plus b (LitI (-i2))
evalBinopExpr e = e

-- Calculates how many atoms the given expression has, without taking into account expressions created because of exception checking
numExprAtoms :: Expr -> Int
numExprAtoms (BinopExpr And e1 e2) = numExprAtoms e1 + numExprAtoms e2
numExprAtoms (BinopExpr Or e1 e2) = numExprAtoms e1 + numExprAtoms e2
numExprAtoms (BinopExpr Implication e1 e2) = numExprAtoms e1 + numExprAtoms e2
numExprAtoms (BinopExpr _ e1 e2) = numExprAtoms e1 + numExprAtoms e2 + 1
numExprAtoms (Parens e) = numExprAtoms e
numExprAtoms (Cond cond e1 e2) = numExprAtoms e2
numExprAtoms LitB {} = 1
numExprAtoms _ = 0

-- Calculates how many atoms the given expression has, taking into account expressions created because of exception checking
numExprAtomsIncCond :: Expr -> Int
numExprAtomsIncCond (BinopExpr And e1 e2) = numExprAtomsIncCond e1 + numExprAtomsIncCond e2
numExprAtomsIncCond (BinopExpr Or e1 e2) = numExprAtomsIncCond e1 + numExprAtomsIncCond e2
numExprAtomsIncCond (BinopExpr Implication e1 e2) = numExprAtomsIncCond e1 + numExprAtomsIncCond e2
numExprAtomsIncCond (BinopExpr _ e1 e2) = numExprAtomsIncCond e1 + numExprAtomsIncCond e2 + 1
numExprAtomsIncCond (Parens e) = numExprAtomsIncCond e
numExprAtomsIncCond (Cond cond e1 e2) = numExprAtomsIncCond cond + numExprAtomsIncCond e1 + numExprAtomsIncCond e2
numExprAtomsIncCond LitB {} = 1
numExprAtomsIncCond _ = 0

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
simplifyExpr (BinopExpr Implication (LitB False) _) = LitB True
simplifyExpr (BinopExpr Implication p expr) = simplifyExpr' (BinopExpr Implication (simplifyExpr p) (simplifyExpr expr))
  where
    simplifyExpr' (BinopExpr Implication (LitB True) expr) = expr
    simplifyExpr' expr = expr
simplifyExpr (BinopExpr Equal (LitB a) (LitB b)) = LitB (a == b)
simplifyExpr (BinopExpr Equal (LitI a) (LitI b)) = LitB (a == b)
simplifyExpr (BinopExpr op expr1 expr2) = BinopExpr op (simplifyExpr expr1) (simplifyExpr expr2)
simplifyExpr (Parens b@(LitB _)) = b
simplifyExpr (Parens e) = Parens (simplifyExpr e)
simplifyExpr (OpNeg (LitB False)) = LitB True
simplifyExpr (OpNeg (LitB True)) = LitB False
simplifyExpr (Cond c e1 e2) = newCond cond
  where
    cond = simplifyExpr c
    expr1 = simplifyExpr e1
    expr2 = simplifyExpr e2
    newCond (LitB True) = expr1
    newCond (LitB False) = expr2
    newCond guard = if expr1 == expr2 then expr1 else Cond guard expr1 expr2
simplifyExpr expr = expr
