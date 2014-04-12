module Solver where

import qualified Data.Map as M
import qualified Data.List as L
import DIMACS
import qualified Debug.Trace as D

{-
- Data Structure
-}

data Solving = Solving {
             _binds :: M.Map Var Bool
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

{-
- one Literal Rule
-}
--単位節を含むか
hasUniteClause :: CNF -> Bool
hasUniteClause (CNF cs)  = any (\x -> case x of
                                       (UnitClause _) -> True
                                       _ -> False) cs

--Clauseを必要であれば変換する
transposeClause :: Clause -> Clause
transposeClause EmptyClause = EmptyClause
transposeClause (Clause ls)
  | lsLength == 0 = EmptyClause
  | lsLength == 1 = UnitClause (head ls)
  | otherwise = Clause ls
  where 
        lsLength = length ls

--inverse Lをリテラルリストから削除する
removeInverseLiteral :: [Literal] -> Literal -> [Literal]
removeInverseLiteral ls l = filter (\x -> x /= (inverse l)) ls

--inverse LをClauseの中のリテラルから削除
removeInverseClauseLiteral :: [Clause] -> Literal -> [Clause]
removeInverseClauseLiteral [] _ = []
removeInverseClauseLiteral (EmptyClause:cs) l = EmptyClause : (removeInverseClauseLiteral cs l)
removeInverseClauseLiteral ((Clause ls):cs) l = (transposeClause (Clause (removeInverseLiteral ls l))) : (removeInverseClauseLiteral cs l)
removeInverseClauseLiteral (u@(UnitClause ll):cs) l
  | ll == inverse l = EmptyClause : removeInverseClauseLiteral cs l --UnitClauseは空になってEmptyClauseに
  | otherwise = u : removeInverseClauseLiteral cs l

--Lをふくむ単位節を削除し、残りの節からもinvert Lを削除する
removeUnitClause :: Solving -> Literal -> Solving
removeUnitClause s l = s { _solving_cnf = newCNF, _binds = newBinds}
  where
    restClause :: [Clause] -> Literal -> [Clause]
    restClause cs ll = filter (\c -> c /= (UnitClause ll)) cs
    newCNF :: CNF
    newCNF = CNF (removeInverseClauseLiteral (restClause (getClause (_solving_cnf s)) l) l)
    newBinds = case l of
                 (Normal i) -> M.insert i True (_binds s)
                 (Not i) -> M.insert i False (_binds s)

removeAllUnitClause :: Solving -> Solving
removeAllUnitClause s = if existsUnitClause then removeAllUnitClause updatedCNF else s
  where
    cnf = _solving_cnf s
    existsUnitClause :: Bool
    existsUnitClause = hasUniteClause cnf
    allUnitClause :: [Clause]
    allUnitClause = filter (\x -> case x of
                                    (UnitClause _) -> True
                                    _ -> False) (getClause cnf)
    allUnitLiteral :: [Literal]
    allUnitLiteral = map (\(UnitClause l) -> l) allUnitClause
    updatedCNF :: Solving
    updatedCNF = L.foldl' (\c v -> removeUnitClause c v) s allUnitLiteral

{-
- Pure literal rule
-}
collectAllLiterals :: [Clause] -> [Literal]
collectAllLiterals cs = L.concat $ L.map (\x -> case x of
                                                 (Clause ls) -> ls
                                                 (UnitClause l) -> [l]
                                                 _ -> []) cs
collectAllPureLiteral :: [Literal] -> [Literal]
collectAllPureLiteral ls = filter (\l -> not ((inverse l) `elem` ls)) ls

--リテラル Lをふくむ節を除去する
removeLiteralClause :: [Clause] -> Literal -> [Clause]
removeLiteralClause [] _ = []
removeLiteralClause (EmptyClause:cs) l = EmptyClause : (removeLiteralClause cs l)
removeLiteralClause (c@(Clause ls):cs) l 
  | l `elem` ls = removeLiteralClause cs l
  | otherwise = c : removeLiteralClause cs l
removeLiteralClause (u@(UnitClause ll):cs) l
  | ll == l = removeLiteralClause cs l
  | otherwise = u : removeLiteralClause cs l

removeAllPureLiteralClause :: Solving -> Solving
removeAllPureLiteralClause s = if null allPureLiteral then s else s {_solving_cnf = CNF newClause, _binds = newBinds}
  where
    cs = (getClause (_solving_cnf s))
    literals :: [Literal]
    literals = collectAllLiterals cs
    allPureLiteral :: [Literal]
    allPureLiteral = L.nub $ collectAllPureLiteral literals
    newClause = L.foldl' removeLiteralClause cs allPureLiteral
    newBinds :: M.Map Var Bool
    newBinds = L.foldl' (\b l -> case l of
                                (Normal i) -> M.insert i True b 
                                (Not i) -> M.insert i False b) (_binds s) allPureLiteral

{-
- クリーンアップ規則
-}
includeTautology :: [Literal] -> Bool
includeTautology ls = any (\l -> (inverse l) `elem` ls) ls

cleanupRule' :: [Clause] -> [Clause]
cleanupRule' [] = []
cleanupRule' (c@(Clause ls):cs) 
  | includeTautology ls = cleanupRule' cs
  | otherwise = c : cleanupRule' cs
cleanupRule' (x:cs) = x : cleanupRule' cs
cleanupRule :: Solving -> Solving
cleanupRule s = s {_solving_cnf = newCNF}
  where
    cnf = _solving_cnf s
    newCNF = CNF (cleanupRule' (getClause cnf))

{-
- 分割規則
-}
--L (Var x)をふくむ節を削除し、残りの節からもinverse Lを削除する
bindAsTrue :: Solving -> Var -> Solving
bindAsTrue s v = s {_solving_cnf = newCNF, _binds = newBinds}
  where
    cs = getClause (_solving_cnf s)
    restClause :: [Clause]
    restClause = filter (\x -> case x of 
                                (UnitClause (Normal v)) -> False
                                (Clause ls) -> not ((Normal v) `elem` ls) --Clauseの中身も確認するところがunit ruleとの違い
                                _ -> True) cs
    newCNF :: CNF
    newCNF = CNF $ removeInverseClauseLiteral restClause (Normal v)
    newBinds = M.insert v True (_binds s)

--inverse L(Var x)をふくむ節を削除し、残りの節からもLを削除する
bindAsFalse :: Solving -> Var -> Solving
bindAsFalse s v = s {_solving_cnf = newCNF, _binds = newBinds}
  where
    cs = getClause (_solving_cnf s)
    restClause :: [Clause]
    restClause = filter (\x -> case x of 
                                (UnitClause (Not v)) -> False
                                (Clause ls) -> not ((Not v) `elem` ls)
                                _ -> True) cs
    newCNF = CNF $ (removeInverseClauseLiteral restClause (Not v))
    newBinds = M.insert v False (_binds s)

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

data Results = Yes Solving | No deriving(Show)

asBoolean :: Results -> Bool
asBoolean (Yes _) = True
asBoolean No = False

satisfiable' :: Solving -> Results
satisfiable' s
    | emptyCNF (_solving_cnf cleanuped) = Yes cleanuped
    | containsEmptyClause (_solving_cnf cleanuped) = No
    | asBoolean trueResults = trueResults
    | asBoolean falseResults = falseResults
    | otherwise = No
  where
    getVar :: Literal -> Var
    getVar (Normal v) = v
    getVar (Not v) = v
    cleanuped :: Solving
    cleanuped = dprint "Cleanuped: " $ removeAllPureLiteralClause $ cleanupRule $ removeAllUnitClause s
    restLiteral = L.nub $ collectAllLiterals $ getClause (_solving_cnf s)
    restVar = L.nub $ L.map getVar restLiteral
    pickupedVar = head restVar
    trueBranch :: Solving
    trueBranch = dprint ("TrueBranch " ++ (show pickupedVar) ++ " -> True : ") $ bindAsTrue cleanuped pickupedVar
    trueResults = satisfiable' trueBranch
    falseBranch :: Solving
    falseBranch = dprint ("False Branch " ++ (show pickupedVar) ++ " -> False : ") $ bindAsFalse cleanuped pickupedVar
    falseResults = satisfiable' falseBranch

satisfiable :: DIMACS -> Results
satisfiable dimacs = results
  where
    cnf = _cnf dimacs
    results = satisfiable' (Solving {_binds = M.empty, _solving_cnf = cnf})
