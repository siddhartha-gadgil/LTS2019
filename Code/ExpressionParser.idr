module ExpressionParser

import Parsers

data Statement : Type where
  Expression: (n: Nat) -> Statement
  Definition: (var: Char) -> (value: Nat) -> Statement


Block : Type
Block = List Statement

getVar : Block -> Char -> Maybe Nat
getVar [] c = Nothing
getVar ((Expression n) :: xs) c = getVar xs c
getVar ((Definition var value) :: xs) c =
  if var == c then Just value else getVar xs c

var : Block -> Parser Nat
var bl s = mapMaybe(letter)(getVar bl)(s)

mutual
  simpleTerm : Block -> Parser Nat
  simpleTerm bl = nat || ((SS "(") <+ (expression bl) +> (SS ")")) || (var bl)

  term : Block -> Parser Nat
  term bl = map(repSepTrim (simpleTerm bl) '*')(foldl(*)(1))

  expression: Block -> Parser Nat
  expression bl = map(repSepTrim (term bl) '+')(foldl(+)(0))

  expr : Block -> Parser Statement
  expr bl = map(expression bl)(Expression)

  defSides: Block -> Parser (Char, Nat)
  defSides bl = ((SS "let ") <+ letter +> (SS "=")) ++ (expression bl)

  defn : Block -> Parser Statement
  defn bl = map(defSides bl)(\p => (case p of
                                         (name, value) => Definition name value))

  stat : Block -> Parser Statement
  stat bl = ((defn bl) || (expr bl)) +> ((SS ";") || map(eof)(\u => ";"))

  emptyBlock : Block -> Parser Block
  emptyBlock bl = map(rep(SS " ") <+ eof)(\u => bl)

  blockRec : Block -> Parser Block
  blockRec bl =
    (emptyBlock bl) ||
    flatMapWithNext(stat bl)(
      \s => blockRec (s :: bl))

block: Parser Block
block = blockRec []

blockValue: Block -> Maybe Nat
blockValue [] = Nothing
blockValue ((Expression n) :: xs) = Just n
blockValue ((Definition var value) :: xs) = Nothing

interpret : String -> ParseResult (Maybe Nat)
interpret s = parse(map(block)(blockValue)) s


eg: ParseResult (Maybe Nat)
eg = interpret "let a = (1 + 2 * (3 + 1)); let b = a + 3 ; a * (b + 1)"
