{-# LANGUAGE StandaloneDeriving #-}
module Solver where

import qualified Data.Map as M
import qualified Data.Monoid as Monoid
import qualified Data.Maybe as Maybe
import qualified Data.List as L
import DIMACS
import qualified Debug.Trace as D
import qualified DAG as G
import qualified Data.Graph.Inductive.Graph as FGL
import qualified Data.Graph.Inductive.Query.Dominators as FDM
import qualified Data.Graph.Inductive.Tree as FT
import qualified Data.Map as M

{-
- Data Structure
-}


data TruthValue = No | Unknown | Yes deriving (Show, Eq, Ord)

type Level = Int

type DecisionFlag = Bool

data Assign = Assign {
            _truthValue :: TruthValue
            ,_level :: Level
            ,_decision :: DecisionFlag
            ,_priority :: Int
            } deriving (Show)

instance Eq Assign where
    a == b = (_truthValue a) == (_truthValue b) && (_level a) == (_level b) && (_decision a) == (_decision b)

instance Ord Assign where
    a `compare` b = ((_truthValue a) `compare` (_truthValue b)) `Monoid.mappend` ((_level a) `compare` (_level b)) `Monoid.mappend` ((_decision a) `compare` (_decision b))

type Assignment = M.Map Var Assign


data ImplicationGraph = ImpGraph {
                                 _graph :: FT.Gr (Var, Assign) Int
                                 ,_node_table :: M.Map (Var, Assign) Int
                                 ,_edge_table :: M.Map (Int, Int) Int
                                 ,_node_counter :: Int
                                 ,_edge_counter :: Int
                                 } deriving (Show)

emptyImplicationGraph :: ImplicationGraph
emptyImplicationGraph = ImpGraph FGL.empty M.empty M.empty 0 0

--ノードの重複は許さない,IDは自動的に割り振る
addNode :: ImplicationGraph -> (Var, Assign) -> ImplicationGraph
addNode g n = if (M.member n (_node_table g)) then
                g
              else
                g {_node_counter = newCounter, _node_table = newNodeTable, _graph = newGraph} 
  where
    newCounter = 1 + (_node_counter g)
    newNodeTable = M.insert n newCounter (_node_table g)
    newGraph = FGL.insNode (newCounter, n) (_graph g) 

--辺の重複は許さない
connect :: ImplicationGraph -> (Var, Assign) -> (Var, Assign) -> ImplicationGraph
connect g f t = if (M.member f (_node_table g)) && (M.member t (_node_table g)) && (not (M.member (fId, tId) (_edge_table g))) then
                  g {_edge_counter = eId, _edge_table = newEdgeTable, _graph = newGraph}
                else 
                  g
  where
    fId = (_node_table g) M.! f
    tId = (_node_table g) M.! t
    eId = 1 + (_edge_counter g)
    newEdgeTable = M.insert (fId, tId) eId (_edge_table g)
    newGraph = FGL.insEdge (fId, tId, eId) (_graph g)

--First UIPを見つける
----そのレベルの決定変数
type RootDecisionVar = (Var, Assign)
type ConflictVar = Var
type UIP = (Var, Assign)
firstUIP :: ImplicationGraph -> RootDecisionVar -> ConflictVar -> FGL.Node
firstUIP g r c = head uipNodes
  where
    rootId :: FGL.Node
    rootId =  (dprint ("Lookup from: " ++ (show (_node_table g))) (_node_table g)) M.! (dprint ("Root: " ++ (show r)) r)
    conflictId :: [FGL.Node]
    conflictId = dprint ("ConflictIds: " ++ (show $ L.map (\(c,_) -> (_node_table g) M.! c) $ M.toList $ M.filterWithKey (\(k, _) _ -> k == c) (_node_table g))) $
                        L.map (\(c,_) -> (_node_table g) M.! c) $ M.toList $ M.filterWithKey (\(k, _) _ -> k == c) (_node_table g)
    dominators :: [[FGL.Node]]
    dominators = dprint ("Dominators: " ++ (show $ L.map (\(_, ns) -> tail ns) $ L.filter (\(n, _) -> n `elem` conflictId) $ FDM.dom (_graph g) rootId)) $
                        L.map (\(_, ns) -> tail ns) $ L.filter (\(n, _) -> n `elem` conflictId) $ FDM.dom (_graph g) rootId
    uipNodes :: [FGL.Node]
    uipNodes = dprint ("UIPNodes is: " ++ show (L.foldl1' (\acc l -> acc `L.intersect` l) dominators)) $ 
                  L.foldl1' (\acc l -> acc `L.intersect` l) dominators

--学習節を求めるための作業をする
{-
- 方法はシンプルに、矛盾している節全ての「理由」を「融合」する。
- 理由は、以下のように求める、
- 含意グラフ上で、自分を指し示しているノードの理由を融合する
- ただし、理由を調べたいノードがFirst UIPならば理由はFirst UIPに割り当てら
- 真理値の反対とする。
- また、理由を調べたいノードが決定変数ならば、同様に割り当てられた真理値の
- 反対とする。
-
- 融合は、以下のように定義する。
- ある２つの節についての融合とは、その節に含まれる、inverseも含めた同値な節
- を削ったものをあらたな節のリテラルとしたものとする
-}

--融合
resolutionClause :: Clause -> Clause -> Clause 
resolutionClause (Clause ls1) (Clause ls2) = Clause $ resolutionLiterals ls1 ls2
  where
    resolutionLiterals :: [Literal] -> [Literal] -> [Literal]
    resolutionLiterals ls1 ls2 = L.nubBy (\a b -> a == b || (inverse a) == b) $ (ls1 ++ ls2)

causeOf :: ImplicationGraph -> FGL.Node -> FGL.Node -> Clause
causeOf g targetNode uipNode
  |targetNode == uipNode || (_decision $ snd targetAssign) || null preNode = let as = targetAssign in
                                                                                if (_truthValue $ snd as) == Yes then 
                                                                                  (Clause [(Not (fst as))])
                                                                                else
                                                                                  (Clause [(Normal (fst as))])
  |otherwise = L.foldl1' (\cold cnew -> (resolutionClause cold cnew))
                  $ L.map (\n -> causeOf g n uipNode) preNode

  where
    getAssign :: ImplicationGraph -> FGL.Node -> (Var, Assign)
    getAssign g n = Maybe.fromJust $ FGL.lab (_graph g) n
    targetAssign :: (Var, Assign)
    targetAssign = getAssign g targetNode
    preNode = FGL.pre (_graph g) targetNode


getLearningClause :: ImplicationGraph -> ConflictVar -> FGL.Node -> Clause
getLearningClause g c uip = L.foldl1' (\cold cnew -> (resolutionClause cold cnew))  $
                              L.map (\cnode -> causeOf g cnode uip) conflictId
  where
    conflictId :: [FGL.Node]
    conflictId = L.map (\(c,_) -> (_node_table g) M.! c) $ M.toList $ M.filterWithKey (\(k, _) _ -> k == c) (_node_table g)

--グラフからあるレベル以上のノードと辺を削除する
cleanupGraph :: ImplicationGraph -> Level -> ImplicationGraph
cleanupGraph g l = g {_graph = newGraph
                     ,_node_table = newNodeTable
                     ,_edge_table = newEdgeTable
                     ,_node_counter = newNodeCounter
                     ,_edge_counter = newEdgeCounter
                     }
  where
    (newNodeTable, matchNodeTable) = M.partitionWithKey (\(_, k) _ -> (_level k) <= l) (_node_table g)
    matchNodes :: [FGL.Node]
    matchNodes = L.map snd $ M.toList matchNodeTable
    (matchEdgeTable, newEdgeTable) = M.partitionWithKey (\(f, t) _ -> (f `elem` matchNodes) || (t `elem` matchNodes)) (_edge_table g)
    matchEdges :: [FGL.Edge]
    matchEdges = L.map fst $ M.toList matchEdgeTable
    newNodeCounter = (_node_counter g) - (length matchNodes)
    newEdgeCounter = (_edge_counter g) - (length matchEdges)
    newGraph = FGL.delEdges matchEdges $ FGL.delNodes matchNodes (_graph g)

--バインドからあるレベル以上のバインドを削る
cleanupBind :: Assignment -> Level -> Assignment
cleanupBind a l = M.map (\as -> if (_level as) > l then as {_truthValue = Unknown, _level = 0, _decision = False} else as) a

--Solvingからあるレベル以上の値を消す
cleanupSolving :: Solving -> Level -> Solving
cleanupSolving s l = s {_implication_graph = cleanupGraph (_implication_graph s) l
                       ,_binds = cleanupBind (_binds s) l
                       }


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

rSortBy :: (a -> a -> Ordering) -> [a] -> [a]
rSortBy = L.sortBy . flip

rSort :: (Ord a) => [a] -> [a]
rSort = rSortBy compare

getClause :: CNF -> [Clause]
getClause (CNF cs) = cs

addClause :: CNF -> Clause -> CNF
addClause (CNF cs) c = (CNF (c : cs))

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


data PropagateResults = Success Solving | Conflict Solving Var deriving (Show)

propagate :: Solving -> Level -> PropagateResults
propagate s dl = if null allUnitClauseData then
                   Success s
                 else
                   if null conflictClauseData then
                     propagate (updateSolving s normalClauseData) dl
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
    --先頭のリテラルと、そのリテラルを含むデータ
    normalClauseData :: [(Literal, [Var])]
    normalClauseData = L.filter (\(l, v) -> l == lit) allUnitClauseData
      where
        lit = fst $ head allUnitClauseData
    --グラフにリテラルと変数のペアのエッジを追加する
    updateGraph :: ImplicationGraph -> Literal  -> [Var] -> Assignment -> ImplicationGraph
    updateGraph g l vs as = L.foldl' (\g from -> connect g (from, (as M.! from))
                                                           ((getVar l), newLAssign))
                                (addNode g ((getVar l), newLAssign)) vs
      where
        lAssign = (as M.! (getVar l))
        newLAssign = lAssign {_truthValue = (getSign l), _level = dl, _decision = False}
    --Solverを更新
    updateSolving :: Solving -> [(Literal, [Var])] -> Solving
    updateSolving s ds = s {_binds = newBinds, _implication_graph = newGraph}
      where
        newBinds = L.foldl' (\b l -> dprint ((strRepeat (dl * 3) " ") ++ "Bind " ++ (show (getVar l)) ++ " to :" ++ (show (getSign l))) $
                                      M.adjust (\as -> as {_truthValue = (getSign l), _level = dl, _decision = False})
                                            (getVar l) b) (_binds s) $ L.map fst ds
        newGraph = L.foldl' (\g (l, vs) -> updateGraph g l vs newBinds) (_implication_graph s) $ dprint ("updateGraphfor: " ++ (show ds)) ds
    

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
- Conflict Analysys
-}
buildFGLGraph :: ImplicationGraph -> Level -> FT.Gr Int Int
buildFGLGraph g dl = undefined

analyze :: Solving -> RootDecisionVar -> ConflictVar -> (Clause, Level, (Var, Assign))
analyze s r conflictVar = (learningClause, jmpLevel, getDesicionVariable)
  where
    uip = firstUIP (_implication_graph s) r conflictVar
    learningClause = getLearningClause (_implication_graph s) conflictVar uip
    literalLevels = rSort $ 0 : (L.nub $ L.map (\v -> (_level ((_binds s) M.! v))) $ L.map getVar (getLiterals learningClause))
    jmpLevel = (dprint ("literalLevels: " ++ show literalLevels) literalLevels)  L.!! 1
    --あるレベルの決定変数を取得
    getDesicionVariable = case M.toList $ M.filter (\a -> (_level a) == jmpLevel && (_decision a)) (_binds s) of
                            [] -> (undefined, undefined)
                            (x:_) -> x
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

satisfiable' :: Solving -> Level -> (Var, Assign) -> Results
satisfiable' s dl (v, as)
  | results == Yes = Sat cleanuped
  | results == No = if dl == 0 then 
                      Unsat 
                    else 
                      dprint ("Learning clause: " ++ (show learningClause) ++ " back to level: " ++ (show jmpLevel)) $
                      satisfiable' learnedSolving jmpLevel (dv, das)
  | otherwise = nextResults
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
                Success x -> dprint ("Eval solving: " ++ (show (evalSolving x))) (evalSolving x)
                Conflict _ _ -> No
    --VSIDS:未決定の変数のうち優先度の高いものから選ぶ
    unknownvars = M.filter (\x -> _truthValue x == Unknown) (_binds cleanuped)
    unknownvar = fst $ head $ rSortBy (\(_, a1) (_, a2) -> compare (_priority a1) (_priority a2)) $ M.toList unknownvars
    --次のブランチ,選んだ未決定の変数に常に偽を割り当てる
    nextBranch = dprint ((strRepeat (dl * 3) " ") ++ "nextBranch: " ++ (show unknownvar)) 
                    $ cleanuped {_binds = (M.adjust (\as -> as {_truthValue = No, _level = (dl + 1), _decision = True})
                                                    unknownvar (_binds cleanuped))
                                 ,_implication_graph = (addNode (_implication_graph cleanuped)
                                                                (unknownvar, (Assign No (dl + 1) True 
                                                                              (_priority ((_binds cleanuped) M.! unknownvar)))))
                                }
    nextResults = satisfiable' nextBranch (dl + 1) (unknownvar, ((_binds nextBranch) M.! unknownvar))
    --解析
    (learningClause, jmpLevel, (dv, das)) = analyze cleanuped (v, as) (getContradictionReason propagated)
    cleanupedSolving = cleanupSolving cleanuped jmpLevel
    learnedSolving = cleanupedSolving {_solving_cnf = (addClause (_solving_cnf cleanupedSolving) learningClause)
                                       ,_binds = L.foldl' (\b v -> (M.adjust (\as -> as {_priority = (_priority as) + 1})
                                                                             v b)) (_binds cleanupedSolving) 
                                                                   (L.map getVar (getLiterals learningClause))
                                                                   }

satisfiable :: DIMACS -> Results
satisfiable dimacs = results
  where
    cnf = _cnf dimacs
    --全ての変数の初期わりあて、全ての変数は最初は未確定の非決定変数の
    --優先度0になっている
    defaultBinds = M.fromList $ [(x, (Assign Unknown 0 False 0)) | x <- [1..(_variableCount dimacs)]]
    results = satisfiable' (Solving {_binds = defaultBinds
                                    ,_solving_cnf = cnf
                                    ,_implication_graph = emptyImplicationGraph}) 0 (undefined, undefined)
