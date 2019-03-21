module ExpressionParser
{- As an illustration to show interpreters are not hard to write, we make
an interpreter for a tiny language with:
  * a single data type: `Nat`
  * arithmetic expressions can have `+`, `*` and parenthesis.
  * assignment statements of the form `let variable = expression`, with variable names being a single character.
-}

import Parsers

-- Statements in our language, these are either expressions or definitions.
data Statement : Type where
  Expression: (n: Nat) -> Statement
  Definition: (var: Char) -> (value: Nat) -> Statement

-- A block (also called context) which is a list of statements but with the last statement the head of the list.
Block : Type
Block = List Statement

-- Getting a variable from a block; if it is defined more than once the last definition is used.
getVar : Block -> Char -> Maybe Nat
getVar [] c = Nothing
getVar ((Expression n) :: xs) c = getVar xs c
getVar ((Definition var value) :: xs) c =
  if var == c then Just value else getVar xs c

-- Parser for a variable name in a context
var : Block -> Parser Nat
var bl s = mapMaybe(letter)(getVar bl)(s)

-- Parsing a block of statements recursively
mutual
  -- A simple term in context: a literal natural number, a variable defined in the context or an expression in parenthesis
  simpleTerm : Block -> Parser Nat
  simpleTerm bl = nat || ((SS "(") <+ (expression bl) +> (SS ")")) || (var bl)

  -- A product of simple terms in context, possibly with just one simple term
  term : Block -> Parser Nat
  term bl = map(repSepTrim (simpleTerm bl) '*')(foldl(*)(1))

  -- A sum of terms in context, possibly with just one term
  expression: Block -> Parser Nat
  expression bl = map(repSepTrim (term bl) '+')(foldl(+)(0))

  -- An arithmetic expression as a statement parsed in context
  expr : Block -> Parser Statement
  expr bl = map(expression bl)(Expression)

  -- Parser for LHS and RHS of a definition in context
  defSides: Block -> Parser (Char, Nat)
  defSides bl = ((SS "let ") <+ letter +> (SS "=")) ++ (expression bl)

  -- Parser for a definition in a context
  defn : Block -> Parser Statement
  defn bl = map(defSides bl)(\p => (case p of
                                         (name, value) => Definition name value))

  -- Parser for a statement in context
  stat : Block -> Parser Statement
  stat bl = ((defn bl) || (expr bl)) +> ((SS ";") || map(eof)(\u => ";"))

  -- Parser for an empty block in context, returns the given context
  emptyBlock : Block -> Parser Block
  emptyBlock bl = map(rep(SS " ") <+ eof)(\u => bl)

  -- Recursively parsing a block given a context
  blockRec : Block -> Parser Block
  blockRec bl =
    (emptyBlock bl) ||
    flatMapWithNext(stat bl)(
      \s => blockRec (s :: bl))

-- Parser for a block, starting with the empty context
block: Parser Block
block = blockRec []

-- The value of a block: the value/rhs of the last statment, defaulting to 0
blockValue: Block -> Nat
blockValue [] = Z
blockValue ((Expression n) :: xs) = n
blockValue ((Definition var value) :: xs) = value

-- Interpret a string and getting the value of the result
interpret : String -> ParseResult Nat
interpret s = parse(map(block)(blockValue)) s

-- An example
eg: ParseResult Nat
eg = interpret "let a = (1 + 2 * (3 + 1)); let b = a + 3 ; a * (b + 1)"
