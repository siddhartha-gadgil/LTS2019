module Lists

%access public export
%default total


--proof that something is an element of the list
isElementOfList : (typ : Type) -> (ls : List typ) -> (a : typ) -> Type
isElementOfList typ ls a = (n : Nat ** (fromMaybe (index' n ls) = a))
