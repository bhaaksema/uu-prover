module WLP where

import Data.Bifunctor (Bifunctor (first))
import Data.Map (Map, adjust, empty, fromList, insert, member, toList, (!))
import ExpressionOps (considerExpr, safeExpressionAndPostcondition, updateExc)
import GCLParser.GCLDatatype
import GeneralTypes
import Z3.Monad

--
-- These functions are for generating the WLP
--

wlp :: Stmt -> PostConditions -> WLPType
wlp (Assert expr) (q, r) vars = first (BinopExpr And safe) evaluatedPost
  where
    (safe, evaluatedPost, safeVars) = safeExpressionAndPostcondition (considerExpr expr vars) (q, r) vars vars
wlp (Assume expr) (q, r) vars = first (BinopExpr Implication (Parens safe) . Parens) evaluatedPost
  where
    (safe, evaluatedPost, safeVars) = safeExpressionAndPostcondition (considerExpr expr vars) (q, r) vars vars
wlp Skip (q, r) vars = q vars
wlp (Seq stmt1 stmt2) (q, r) vars = do
  let stmt2Q = wlp stmt2 (q, r)
  let stmt1Q = wlp stmt1 (stmt2Q, r)
  stmt1Q vars
wlp (Assign name expr) (q, r) vars = do
  let q' = if name == "exc" then r else q
  let basicUpdate = insert name expr vars -- Update the value of this variable to the expression
  let arrayLengthUpdate = insert ("#" ++ name) (vars ! ("#" ++ getArrayName expr)) basicUpdate
  let isArray = member ("#" ++ name) vars
  let newVars = if isArray then arrayLengthUpdate else basicUpdate

  let (value, evaluatedPost, safeVars) = safeExpressionAndPostcondition (considerExpr expr vars) (q', r) vars newVars
  evaluatedPost
  where
    getArrayName (Var name) = name -- Get name of the variable
    getArrayName (RepBy expr _ _) = getArrayName expr -- Unwrap RepBy to get the name of the original array (we need it to find the length variable later on)
    getArrayName expr = error "Trying to get array name from variable that is not an array: " ++ show expr
wlp (AAssign name indexE expr) (q, r) vars = do
  let array = vars ! name
  let lowerBound = BinopExpr LessThan indexE (LitI 0)
  let upperBound = BinopExpr GreaterThanEqual indexE (Var $ "#" ++ name)
  let newVars' = insert name (RepBy array indexE expr) vars -- This will only be used if the expression cannot throw an error
  let newVars = updateExc (BinopExpr Or lowerBound upperBound) (LitI 2) newVars'

  let (_, _, safeVars) = safeExpressionAndPostcondition (considerExpr expr vars) (q, r) vars newVars
  let (_, evaluatedPost, _) = safeExpressionAndPostcondition (considerExpr indexE vars) (q, r) vars safeVars
  evaluatedPost
wlp s _ _ = error ("Unknown statement '" ++ show s ++ "'")

-- Returns a list of all variables declared in the program
findLocvars :: Stmt -> [VarDeclaration]
findLocvars (Seq stmt1 stmt2) = findLocvars stmt1 ++ findLocvars stmt2
findLocvars (While _ stmt) = findLocvars stmt
findLocvars (IfThenElse _ stmt1 stmt2) = findLocvars stmt1 ++ findLocvars stmt2
findLocvars (Block vars stmt) = vars ++ findLocvars stmt
findLocvars (TryCatch excName tryBlock catchBlock) = VarDeclaration excName (PType PTInt) : findLocvars tryBlock ++ findLocvars catchBlock
findLocvars _ = []

traceVarExpr :: Stmt -> GCLVars -> GCLVars
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
