module DIMACS where

type VarId = Int
data Var = Var VarId deriving (Show, Eq, Ord)

data Literal = Not Var | Normal Var deriving (Show, Eq)

data Clause = EmptyClause | Clause [Literal] | UnitClause Literal deriving (Show, Eq)

data CNF = CNF [Clause] deriving (Show)

type VariableCount = Int
type ClauseCount = Int
data Header = Header VariableCount ClauseCount deriving (Show)

data DIMACS = DIMACS {
            _variableCount :: VariableCount
            ,_clauseCount :: ClauseCount
            ,_cnf :: CNF
            } deriving (Show)
