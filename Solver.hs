module Solver where

import qualified Data.Map as M
import qualified Data.List as L
import DIMACS
import qualified Debug.Trace as D

{-
- Data Structure
-}


data TruthValue = No | Unknown | Yes deriving (Show, Eq, Ord)

type Level = Int

type DecisionFlag = Bool
data Assign = Assign {
            _truthValue :: TruthValue
            ,_level :: Level
            ,_deicision :: DecisionFlag
            } deriving (Show, Eq)
type Assignment = M.Map Var Assign

data Solving = Solving {
             _binds :: Assignment
             ,_solving_cnf :: CNF
             } deriving (Show)

{-
- Utility functions
-}
getClause :: CNF -> [Clause]
getClause (CNF cs) = cs

inverse :: Literal -> Literal
inverse (Normal v) = (Not v)
inverse (Not v) = (Normal v)

getVar :: Literal -> Var
getVar (Normal v) = v
getVar (Not v) = v

getSign :: Literal -> TruthValue
getSign (Normal _) = Yes
getSign (Not _) = No

{-
- Evaluate Function
-}

evalLiteral :: Literal -> Assignment -> TruthValue
evalLiteral (Normal v) as = _truthValue $ as M.! v
evalLiteral (Not v) as
  | assign == Unknown = Unknown
  | assign == Yes = No
  | assign == No = Yes
  where
    assign = _truthValue $ as M.! v

evalClause :: Clause -> Assignment -> TruthValue
evalClause EmptyClause _  = No
evalClause (Clause ls) as = maximum (No : L.map (\l -> evalLiteral l as) ls)

evalSolving :: Solving -> TruthValue
evalSolving s = minimum (Yes : L.map (\c -> evalClause c (_binds s)) clauses)
  where
    clauses = getClause $ _solving_cnf s

{-
- one Literal Rule
-}
findUnitLiteral :: [(Literal, TruthValue)] -> Maybe Literal -> Maybe Literal
findUnitLiteral [] tmp = tmp
findUnitLiteral ((l, Unknown):ls) Nothing = findUnitLiteral ls (Just l)
findUnitLiteral ((_, Unknown):_) (Just _) = Nothing
findUnitLiteral ((_, Yes):_) _ = Nothing
findUnitLiteral ((_, No):ls) tmp = findUnitLiteral ls tmp

--単位節かどうか
isUnitClause :: Clause -> Assignment -> Maybe Literal
isUnitClause EmptyClause _ = Nothing
isUnitClause (Clause ls) as = findUnitLiteral evalResults Nothing
  where
    evalResults = L.map (\l -> (l, (evalLiteral l as))) ls


propagate :: Solving -> Level -> Solving
propagate s dl = case unitClause of
                Just c -> if evalResults /= No then propagate (newSolving s c) dl else s
                Nothing -> s
  where
    cs = getClause $ _solving_cnf s
    evalResults = evalSolving s
    unitClause = L.find (\c -> case isUnitClause c (_binds s) of
                                 Just s -> True
                                 Nothing -> False) cs
    unitLiteral :: Clause -> Assignment -> Literal
    unitLiteral (Clause ls) as = head $ filter (\l -> (evalLiteral l as) == Unknown) ls
    newSolving :: Solving -> Clause -> Solving
    newSolving s c = s {_binds = (M.insert (getVar (unitLiteral c (_binds s))) 
                                           (Assign (getSign (unitLiteral c (_binds s))) dl False)
                                           (_binds s)) }
  

{-
- Pure literal rule
-}
--collectAllLiterals :: [Clause] -> [Literal]
--collectAllLiterals cs = L.concat $ L.map (\x -> case x of
--                                                 (Clause ls) -> ls
--                                                 (UnitClause l) -> [l]
--                                                 _ -> []) cs
--collectAllPureLiteral :: [Literal] -> [Literal]
--collectAllPureLiteral ls = filter (\l -> not ((inverse l) `elem` ls)) ls
--
----リテラル Lをふくむ節を除去する
--removeLiteralClause :: [Clause] -> Literal -> [Clause]
--removeLiteralClause [] _ = []
--removeLiteralClause (EmptyClause:cs) l = EmptyClause : (removeLiteralClause cs l)
--removeLiteralClause (c@(Clause ls):cs) l 
--  | l `elem` ls = removeLiteralClause cs l
--  | otherwise = c : removeLiteralClause cs l
--removeLiteralClause (u@(UnitClause ll):cs) l
--  | ll == l = removeLiteralClause cs l
--  | otherwise = u : removeLiteralClause cs l
--
--removeAllPureLiteralClause :: Solving -> Solving
--removeAllPureLiteralClause s = if null allPureLiteral then s else s {_solving_cnf = CNF newClause, _binds = newBinds}
--  where
--    cs = (getClause (_solving_cnf s))
--    literals :: [Literal]
--    literals = collectAllLiterals cs
--    allPureLiteral :: [Literal]
--    allPureLiteral = L.nub $ collectAllPureLiteral literals
--    newClause = L.foldl' removeLiteralClause cs allPureLiteral
--    newBinds :: Assignment
--    newBinds = L.foldl' (\b l -> case l of
--                                (Normal i) -> M.insert i Yes b 
--                                (Not i) -> M.insert i No b) (_binds s) allPureLiteral

{-
- クリーンアップ規則
-}
--includeTautology :: [Literal] -> Bool
--includeTautology ls = any (\l -> (inverse l) `elem` ls) ls
--
--cleanupRule' :: [Clause] -> [Clause]
--cleanupRule' [] = []
--cleanupRule' (c@(Clause ls):cs) 
--  | includeTautology ls = cleanupRule' cs
--  | otherwise = c : cleanupRule' cs
--cleanupRule' (x:cs) = x : cleanupRule' cs
--cleanupRule :: Solving -> Solving
--cleanupRule s = s {_solving_cnf = newCNF}
--  where
--    cnf = _solving_cnf s
--    newCNF = CNF (cleanupRule' (getClause cnf))

{-
- 分割規則
-}
--L (Var x)をふくむ節を削除し、残りの節からもinverse Lを削除する
--bindAsTrue :: Solving -> Var -> Solving
--bindAsTrue s v = s {_solving_cnf = newCNF, _binds = newBinds}
--  where
--    cs = getClause (_solving_cnf s)
--    restClause :: [Clause]
--    restClause = filter (\x -> case x of 
--                                (UnitClause (Normal v)) -> False
--                                (Clause ls) -> not ((Normal v) `elem` ls) --Clauseの中身も確認するところがunit ruleとの違い
--                                _ -> True) cs
--    newCNF :: CNF
--    newCNF = CNF $ removeInverseClauseLiteral restClause (Normal v)
--    newBinds = M.insert v Yes (_binds s)
--
----inverse L(Var x)をふくむ節を削除し、残りの節からもLを削除する
--bindAsFalse :: Solving -> Var -> Solving
--bindAsFalse s v = s {_solving_cnf = newCNF, _binds = newBinds}
--  where
--    cs = getClause (_solving_cnf s)
--    restClause :: [Clause]
--    restClause = filter (\x -> case x of 
--                                (UnitClause (Not v)) -> False
--                                (Clause ls) -> not ((Not v) `elem` ls)
--                                _ -> True) cs
--    newCNF = CNF $ (removeInverseClauseLiteral restClause (Not v))
--    newBinds = M.insert v No (_binds s)

{-
- 充足可能性
-}
emptyCNF :: CNF -> Bool
emptyCNF (CNF []) = True
emptyCNF _ = False

containsEmptyClause :: CNF -> Bool
containsEmptyClause (CNF cs) = any (\c -> c == EmptyClause) cs

dprint :: (Show a) => String -> a -> a
--dprint msg x = D.trace (msg ++ (show x)) x
dprint msg x = x

data Results = Sat Solving | Unsat deriving(Show)

asBoolean :: Results -> Bool
asBoolean (Sat _) = True
asBoolean Unsat = False

satisfiable' :: Solving -> Level -> Results
satisfiable' s dl
  | results == Yes = Sat cleanuped
  | results == No = Unsat 
  | asBoolean trueResults = trueResults
  | asBoolean falseResults = falseResults
  | otherwise = Unsat
  where
    cleanuped :: Solving
    cleanuped = dprint "cleanuped: " $ propagate s dl
    results = evalSolving cleanuped
    unknownvars = M.filter (\x -> _truthValue x == Unknown) (_binds cleanuped)
    unknownvar = head $ M.keys unknownvars
    trueBranch = dprint "trueBranch: " $ cleanuped {_binds = (M.insert unknownvar (Assign Yes dl True) (_binds cleanuped))}
    trueResults = satisfiable' trueBranch (dl + 1)
    falseBranch = dprint "falseBranch :" $ cleanuped {_binds = (M.insert unknownvar (Assign No dl True) (_binds cleanuped))}
    falseResults = satisfiable' falseBranch (dl + 1)

satisfiable :: DIMACS -> Results
satisfiable dimacs = results
  where
    cnf = _cnf dimacs
    defaultBinds = M.fromList $ [(x, (Assign Unknown 0 False)) | x <- [1..(_variableCount dimacs)]]
    results = satisfiable' (Solving {_binds = defaultBinds, _solving_cnf = cnf}) 0
