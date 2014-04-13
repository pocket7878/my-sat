module Solver where

import qualified Data.Map as M
import qualified Data.Maybe as Maybe
import qualified Data.List as L
import DIMACS
import qualified Debug.Trace as D
import qualified DAG as G

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
            } deriving (Show, Eq, Ord)

type Assignment = M.Map Var Assign

type ImplicationGraph = G.Graph (Var, Assign) 

data Solving = Solving {
             _implication_graph :: ImplicationGraph
             ,_binds :: Assignment
             ,_solving_cnf :: CNF
             } deriving (Show)

{-
- Utility functions
-}
strRepeat :: Int -> String -> String
strRepeat 0 _ = ""
strRepeat n str = str ++ (strRepeat (n - 1) str)

getClause :: CNF -> [Clause]
getClause (CNF cs) = cs

getLiterals :: Clause -> [Literal]
getLiterals (Clause ls) = ls

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
isUnitClause (Clause ls) as = findUnitLiteral evalResults Nothing
  where
    evalResults = L.map (\l -> (l, (evalLiteral l as))) ls


data PropagateResults = Success Solving | Conflict Solving Var

propagate :: Solving -> Level -> PropagateResults
propagate s dl = if null allUnitClauseData then
                   Success s
                 else
                   if null conflictClauseData then
                     propagate (updateSolving s allUnitClauseData) dl
                   else
                     Conflict (updateSolving s conflictClauseData) $ getVar (Maybe.fromJust conflictLiteral)
                     
  where
    --全ての節
    allClause = getClause $ _solving_cnf s
    --単位リテラルとその節に含まれる残りの変数のリストのペアを集めたもの
    allUnitClauseData :: [(Literal, [Var])]
    allUnitClauseData = Maybe.catMaybes $ L.map (\c -> case isUnitClause c (_binds s) of
                                                        Just l -> Just (l, L.map (\ll -> (getVar ll)) 
                                                                            (L.filter (\ll -> ll /= l) (getLiterals c)))
                                                        Nothing -> Nothing) allClause
    --単位リテラルリスト
    unitLiterals = L.map fst allUnitClauseData
    --その単位リテラル中でコンフリクトしているものを一つ取り出す
    --allUnitClauseDataの中で、自分とinverseのリテラルを含むものがallUnitClauseDataのなかに入っているもの
    conflictLiteral :: Maybe Literal
    conflictLiteral = L.find (\l -> (any (\ll -> ll == (inverse l)) unitLiterals)) unitLiterals
    --そのようなリテラルのデータペアを取り出す
    conflictClauseData :: [(Literal, [Var])]
    conflictClauseData = case conflictLiteral of
                           Just l -> L.filter (\(ul, c) -> ul == l || ul == (inverse l)) allUnitClauseData
                           Nothing -> []
    --グラフにリテラルと変数のペアのエッジを追加する
    updateGraph :: ImplicationGraph -> Literal  -> [Var] -> Assignment -> ImplicationGraph
    updateGraph g l vs as = L.foldl' (\g from -> G.connect g
                                                           (G.Vertex  (from, (as M.! from)))
                                                           (G.Vertex  ((getVar l), (Assign (getSign l) dl False))))
                                (G.addVertex g (G.Vertex ((getVar l), (Assign (getSign l) dl False)))) vs
    --Solverを更新
    updateSolving :: Solving -> [(Literal, [Var])] -> Solving
    updateSolving s ds = s {_binds = newBinds, _implication_graph = newGraph}
      where
        newBinds = L.foldl' (\b l -> dprint ((strRepeat (dl * 3) " ") ++ "Bind " ++ (show (getVar l)) ++ " to :" ++ (show (getSign l))) $
                                      M.insert (getVar l) (Assign (getSign l) dl False) b) (_binds s) $ L.map fst ds
        newGraph = L.foldl' (\g (l, vs) -> updateGraph g l vs newBinds) (_implication_graph s) ds
    

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

dprint :: (Show a) => String -> a -> a
dprint msg x = D.trace msg x
--dprint msg x = x

data Results = Sat Solving | Unsat deriving(Show)

asBoolean :: Results -> Bool
asBoolean (Sat _) = True
asBoolean Unsat = False

satisfiable' :: Solving -> Level -> Results
satisfiable' s dl
  | results == Yes = Sat cleanuped
  | results == No = if dl == 0 then Unsat else dprint ("ContradictionReason: " ++ (show (getContradictionReason propagated)) 
                                                       ++ " and Graph: \n" ++ (show (_implication_graph cleanuped))) Unsat
  | asBoolean trueResults = trueResults
  | asBoolean falseResults = falseResults
  | otherwise = Unsat
  where
    propagated :: PropagateResults
    propagated = propagate s dl
    cleanuped :: Solving
    cleanuped = getSolving propagated
    getContradictionReason :: PropagateResults -> Var
    getContradictionReason (Success s) = error "Not in contradiction"
    getContradictionReason (Conflict s v) = v
    getSolving :: PropagateResults -> Solving
    getSolving (Success s) = s
    getSolving (Conflict s v) = s
    results = case propagated of
                Success s -> evalSolving s
                Conflict s v -> No
    unknownvars = M.filter (\x -> _truthValue x == Unknown) (_binds cleanuped)
    unknownvar = head $ M.keys unknownvars
    trueBranch = dprint ((strRepeat (dl * 3) " ") ++ "trueBranch: " ++ (show unknownvar)) 
                      $ cleanuped {_binds = (M.insert unknownvar (Assign Yes dl True) (_binds cleanuped))
                                  ,_implication_graph = (G.addVertex (_implication_graph cleanuped)
                                  (G.Vertex (unknownvar, (Assign Yes dl True))))}
    trueResults = satisfiable' trueBranch (dl + 1)
    falseBranch = dprint ((strRepeat (dl * 3) " ") ++ "falseBranch: " ++ (show unknownvar)) 
                    $ cleanuped {_binds = (M.insert unknownvar (Assign No dl True) (_binds cleanuped))}
    falseResults = satisfiable' falseBranch (dl + 1)

satisfiable :: DIMACS -> Results
satisfiable dimacs = results
  where
    cnf = _cnf dimacs
    defaultBinds = M.fromList $ [(x, (Assign Unknown 0 False)) | x <- [1..(_variableCount dimacs)]]
    results = satisfiable' (Solving {_binds = defaultBinds
                                    ,_solving_cnf = cnf
                                    ,_implication_graph = G.empty}) 0
