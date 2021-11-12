module GeneralTypes where

import Data.Map (Map)
import GCLParser.GCLDatatype (Expr, Stmt, Type)
import Z3.Monad (AST, Z3)

type PathStatements = [Stmt]

type GCLVars = Map String Expr

type VarTypes = Map String Type

type Z3Vars = Map String (Z3 AST)

type ExceptionCode = Integer

type Condition = Expr

type WLPType = GCLVars -> (Expr, GCLVars)

type PostCondition = WLPType

type PostConditions = (WLPType, WLPType)
