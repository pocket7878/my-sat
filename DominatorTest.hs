module Main where

import qualified Data.Graph.Inductive.Graph as G
import qualified Data.Graph.Inductive.Query.Dominators as D
import qualified Data.Graph.Inductive.Tree as T

--BuildGraph
nodes :: [G.LNode String]
nodes = [(x, ("Var " ++ show x)) | x <- [1..9]]

edges :: [G.LEdge Int]
edges = [(1,2,1)
        ,(1,3,2)
        ,(2,4,3)
        ,(3,4,4)
        ,(4,5,5)
        ,(5,6,6)
        ,(5,7,7)
        ,(6,8,8)
        ,(7,8,9)
        ,(7,9,10)]


testGraph :: T.Gr String Int
testGraph = G.mkGraph nodes edges

main :: IO ()
main = do {
          putStrLn $ show $ D.dom testGraph 1;
          putStrLn $ show $ D.iDom testGraph 1;
          putStrLn $ show $ G.match 5 testGraph;
          putStrLn "";
          putStrLn $ show $ G.context testGraph 5;
          }
