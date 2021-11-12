module GeneralTypes where

import GCLParser.GCLDatatype (Expr, Stmt)

type PathStatements = [Stmt]

type ExceptionCode = Integer

type Condition = Expr