module Graphexamples

import Graph
import Data.Vect

am1 :(Vect 6 (Vect 6  Nat))
am1 = [[0,1,1,0,0,0],[1,0,1,0,0,0],[1,1,0,0,0,0],[0,0,0,0,1,0],[0,0,0,1,0,1],[0,0,0,0,1,0]]
am2:(Vect 6 (Vect 6  Nat))
am2 = [[0,1,1,0,0,0],[1,0,1,1,0,0],[1,1,0,0,0,1],[0,1,0,0,1,0],[0,0,0,1,0,1],[0,0,1,0,1,0]]
am3:(Vect 6 (Vect 6  Nat))
am3=[[0,1,1,0,0,0],[1,0,1,1,0,0],[1,1,0,0,0,0],[0,1,0,0,1,0],[0,0,0,1,0,0],[0,0,0,0,0,0]]
am4 : (Vect 8 (Vect 8  Nat))
am4 = [[0,1,1,0,0,0,0,0],[1,0,1,0,1,0,0,1],[1,1,0,1,0,0,0,0],[0,0,1,0,1,0,1,0],[0,1,0,1,0,1,1,0],[0,0,0,0,1,0,1,0],[0,0,0,1,1,1,0,0],[0,1,0,0,0,0,0,0]]

ConnectedComponents_of_am1 : List (List Nat )
ConnectedComponents_of_am1 = (ConnectedComponents am1)--[[6,5,4],[3,2,1]]

ConnectedComponents_of_am3 : List (List Nat )
ConnectedComponents_of_am3 = ConnectedComponents am3

Path_am4_2_7:Maybe  ( List Nat)
Path_am4_2_7 = (FindPath am4 2 7 )--Just ([2,1,3,4,7])


Path_am1_2_5:Maybe  ( List Nat)
Path_am1_2_5 = (FindPath am1 2 5 )--Nothing


PathProof_am4_2_7 :Maybe((List Nat),Path am4 2 7 )
PathProof_am4_2_7 = PathWithProof am4 2 7--Returns Path between 2 and 7 and a proof that it is a path.

PathProof_am1_2_5 :Maybe((List Nat),Path am1 2 5 )
PathProof_am1_2_5 = PathWithProof am1 2 5
