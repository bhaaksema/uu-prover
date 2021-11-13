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

safeExpressionAndPostcondition :: Expr -> PostConditions -> GCLVars -> GCLVars -> (Expr, (Expr, GCLVars), GCLVars)
safeExpressionAndPostcondition expr (q, r) originalVariables postcondVariables = (safeExpr, qrSelector, safeVars)
  where
    (safeExpr, safeVars) = safeExpression expr originalVariables
    newExcValue = safeVars ! "exc"
    postcondVariables' = insert "exc" newExcValue postcondVariables
    (ifQ, qVars) = q postcondVariables'
    (ifR, rVars) = r postcondVariables'
    -- Will select the correct post condition (q or r) depending on what the exc value is
    qrSelector = (changeIf excZero ifQ ifR, combinedVars)
    -- Now: Combine qVars and rVars st every value becomes \(qValue,rValue) -> if noError qValue else rValue
    combinedVars = mapWithKey (\name value -> changeIf excZero value (rVars ! name)) qVars
    excZero = BinopExpr Equal (safeVars ! "exc") (LitI 0)

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
safeExpression e@NewStore {} vars = (e, vars) -- This is a wrapper for an if-then-else, thus we just pass the value along
safeExpression e _ = error ("Cannot determinte if expression would result in exception: '" ++ show e ++ "'")

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

-- Calculates how many atoms the given expression has, without taking into account expressions created because of exception checking
numExprAtoms :: Expr -> Int
numExprAtoms (BinopExpr And e1 e2) = numExprAtoms e1 + numExprAtoms e2
numExprAtoms (BinopExpr Or e1 e2) = numExprAtoms e1 + numExprAtoms e2
numExprAtoms (BinopExpr Implication e1 e2) = numExprAtoms e1 + numExprAtoms e2
numExprAtoms (BinopExpr _ e1 e2) = numExprAtoms e1 + numExprAtoms e2 + 1
numExprAtoms (Parens e) = numExprAtoms e
numExprAtoms (NewStore (RepBy cond e1 e2)) = numExprAtoms e1
numExprAtoms LitB{} = 1
numExprAtoms _ = 0

-- Calculates how many atoms the given expression has, taking into account expressions created because of exception checking
numExprAtomsIncRepby :: Expr -> Int
numExprAtomsIncRepby (BinopExpr And e1 e2) = numExprAtomsIncRepby e1 + numExprAtomsIncRepby e2
numExprAtomsIncRepby (BinopExpr Or e1 e2) = numExprAtomsIncRepby e1 + numExprAtomsIncRepby e2
numExprAtomsIncRepby (BinopExpr Implication e1 e2) = numExprAtomsIncRepby e1 + numExprAtomsIncRepby e2
numExprAtomsIncRepby (BinopExpr _ e1 e2) = numExprAtomsIncRepby e1 + numExprAtomsIncRepby e2 + 1
numExprAtomsIncRepby (Parens e) = numExprAtomsIncRepby e
numExprAtomsIncRepby (NewStore (RepBy cond e1 e2)) = numExprAtomsIncRepby cond + numExprAtomsIncRepby e1 + numExprAtomsIncRepby e2
numExprAtomsIncRepby LitB{} = 1
numExprAtomsIncRepby _ = 0

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
