module Graph_alt

import Data.Fin
import Data.Vect
import fn_to_vect
import Matrix

||| Definition of a graph as it's adacency matrix
total
Graph : (n : Nat) -> Type
Graph n = Mat_Vect n n Bool

total
self_loops : (n : Nat) -> (Graph n)
self_loops n = Identity_Bool n

total
or : Bool -> Bool -> Bool
or False False = False
or _ _ = True

total
and : Bool -> Bool -> Bool
and True True = True
and _ _ = False

total
add_self_loops : (n : Nat) -> (Graph n) -> (Graph n)
add_self_loops n adj = addMat n n Bool or adj (self_loops n)

total
mulGraphs : (n : Nat) -> (Graph n) -> (Graph n) -> (Graph n)
mulGraphs n u v = ( mulMat n n n Bool and or False u v )

total
nth_power_of_adj : (n : Nat) -> (siz : Nat) -> (Graph siz) -> (Graph siz)
nth_power_of_adj Z siz adj = self_loops siz
nth_power_of_adj (S k) siz adj =
      mulGraphs siz adj (nth_power_of_adj k siz adj)

total
Is_path_of_length : (length : Nat) -> (siz : Nat) -> (Graph siz) ->
                    (i : Fin siz) -> (j : Fin siz) -> Bool
Is_path_of_length l siz adj i j =
      index j (index i (nth_power_of_adj l siz adj ))
