module ImplicationGraph where

import qualified Data.Graph.Inductive.Graph as FGL
import qualified Data.Graph.Inductive.Query.Dominators as FDM
import qualified Data.Graph.Inductive.Tree as FT
import qualified Data.Map as M
import DIMACS

type ImplicationGraph = ImpGraph {
                                 _graph :: FT.Gr Int Int
                                 ,_table :: M.Map Int -> (Var, Assign)
                                 ,_node_counter :: Int
                                 ,_edge_counter :: Int
                                 }

