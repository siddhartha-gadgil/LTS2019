module Graphexamples

import Graph
import Data.Vect

Am1 :(Vect 6 (Vect 6  Nat))
Am1 = [[0,1,1,0,0,0],[1,0,1,0,0,0],[1,1,0,0,0,0],[0,0,0,0,1,0],[0,0,0,1,0,1],[0,0,0,0,1,0]]
Am2:(Vect 6 (Vect 6  Nat))
Am2 = [[0,1,1,0,0,0],[1,0,1,1,0,0],[1,1,0,0,0,1],[0,1,0,0,1,0],[0,0,0,1,0,1],[0,0,1,0,1,0]]
Am3:(Vect 6 (Vect 6  Nat))
Am3=[[0,1,1,0,0,0],[1,0,1,1,0,0],[1,1,0,0,0,0],[0,1,0,0,1,0],[0,0,0,1,0,0],[0,0,0,0,0,0]]
Am4 : (Vect 8 (Vect 8  Nat))
Am4 = [[0,1,1,0,0,0,0,0],[1,0,1,0,1,0,0,1],[1,1,0,1,0,0,0,0],[0,0,1,0,1,0,1,0],[0,1,0,1,0,1,1,0],[0,0,0,0,1,0,1,0],[0,0,0,1,1,1,0,0],[0,1,0,0,0,0,0,0]]

ConnectedComponents_of_Am1 : List (List Nat )
ConnectedComponents_of_Am1 = (ConnectedComponents Am1)--[[6,5,4],[3,2,1]]

ConnectedComponents_of_Am3 : List (List Nat )
ConnectedComponents_of_Am3 = ConnectedComponents Am3

Path_Am4_2_7:Maybe  ( List Nat)
Path_Am4_2_7 = (FindPath Am4 2 7 )--Just ([2,1,3,4,7])


Path_Am1_2_5:Maybe  ( List Nat)
Path_Am1_2_5 = (FindPath Am1 2 5 )--Nothing


PathProof_Am4_2_7 :Maybe((List Nat),Path Am4 2 7 )
PathProof_Am4_2_7 = PathWithProof Am4 2 7--Returns Path between 2 and 7 and a proof that it is a path.

PathProof_Am1_2_5 :Maybe((List Nat),Path Am1 2 5 )
PathProof_Am1_2_5 = PathWithProof Am1 2 5
