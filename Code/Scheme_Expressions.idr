module Scheme_Expressions

import Scheme_Parsers

data Statement : Type where
    Expression : Nat -> Statement
    Definition : (var : Char) -> (value : Nat) -> Statement
    Function : (fun : Char) -> (expr : (Nat -> Nat)) -> Statement
     
