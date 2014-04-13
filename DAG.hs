module DAG where

import qualified Data.Set as S

data Vertex a = Vertex a deriving (Show, Eq, Ord)

data Edge a = Edge (Vertex a) (Vertex a) deriving (Show, Eq, Ord)

data Graph a = Graph (S.Set (Vertex a)) (S.Set (Edge a)) deriving (Show, Eq)

empty :: Graph a
empty = Graph S.empty S.empty

addVertex :: (Ord a) => Graph a -> Vertex a -> Graph a
addVertex (Graph vs es) v = Graph (S.insert v vs) es

addEdge :: (Ord a) => Graph a -> Edge a -> Graph a
addEdge (Graph vs es) e = Graph vs (S.insert e es)

connect :: (Ord a) => Graph a -> Vertex a -> Vertex a -> Graph a
connect g from to = addEdge g (Edge from to)
