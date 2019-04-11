module Scheme_Expressions

import Scheme_Parsers

||| The type of curried function on double
Curried_fn : (n : Nat) -> Type
Curried_fn Z = Double
Curried_fn (S n) = Double -> (Curried_fn n)

||| Type of expressions 
data Statement : Type where
    Expression : Double -> Statement
    Definition : (var : Char) -> (value : Double) -> Statement
    Function : (n : Nat) -> (Curried_fn n) -> Statement
     
