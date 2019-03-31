module Parsers
{-
Parsing is the conversion of input, say a list of characters or a string,
to structured data, if the input is of the appropriate form. We implement here
the idea of _combinator parsing_, where we build parsers from basic ones by
combining and transforming parsers.

This allows us to parse relatively complex languages with a small amount of code.
Better still, even the code to enable this is small (at least provided we do not
address issues of efficiency and error messages).
-}

%access public export

{- The result of parsing, either consuming some input and generating a result
with type `a` as well as the rest of the input, or reporting that parsing failed.
-}
data ParseResult : Type -> Type where
  Success : {a: Type} -> (result : a) -> (rest: List Char) -> ParseResult a
  Failed : {a: Type} ->  ParseResult a

-- A parser, which takes input and gives a result (plus unconsumed input)
Parser: Type -> Type
Parser a = (List Char) -> ParseResult a

-- A helper method
parseChars : {a: Type} -> Parser a -> List Char -> ParseResult a
parseChars  p xs = p xs

-- A helper that allows giving a string as method to parse: the most user-friendly method
parse : {a: Type} -> Parser a -> String -> ParseResult a
parse p s = parseChars p (unpack s)

-- A parser that checks if a character satisfies a predicate and returns it.
charPred : (Char -> Bool) -> Parser Char
charPred p l = (case l of
                     [] => Failed
                     (x :: xs) =>
                       if (p x) then (Success x xs) else Failed)

-- A parser matching a specific character
charLit : Char -> Parser Char
charLit c = charPred (\x => x == c)

{- Given a parser `p` for type `a` and a function `f: a -> b` gives a parser for type `b`;
this succeeds if `p` succeeds, and the result for type `b` is obtained by applying `f`
to the result of `p`
-}
map : {a: Type} -> {b: Type} -> Parser a -> (a -> b) -> Parser b
map p f cs = (case (p cs) of
                           (Success  result rest) => Success  (f result) rest
                           Failed => Failed)

{- Given parsers `p` for type `a` and `q` for type `b`, returns a parser which
parses the input on `a`, and if this succeeds parses the rest with `q`. A success
is where both parses succeed, and the result is the pair of results.
-}
(++) : {a : Type} -> {b: Type} -> Parser a -> Parser b -> Parser (Pair a b)
(++) p q l = (case p l of
                       (Success result1 rest1) =>
                          (case (q rest1) of
                              (Success result2 rest2) => Success ((result1, result2)) rest2
                              Failed => Failed)
                       Failed => Failed)


{- A parser that matches a list of characters, e.g. [`l`, `e`, `t`]. This means
the input should begin with this. This could have been reursively implemented
with `charLit` and `(++)` instead.
-}
charsLit: (List Char) -> Parser (List Char)
charsLit []  l = Success [] l
charsLit (x :: xs) [] = Failed
charsLit (x :: xs) (a :: bs) =
                  (case charLit x (a :: bs) of
                        (Success result1 rest) => (case (charsLit xs bs) of
                                (Success result2 rest) => Success (result1 :: result2) rest
                                Failed => Failed)
                        Failed => Failed)


-- A parser matching a string, e.g. "let"
S: String -> Parser String
S s = map (charsLit (unpack s)) pack

{- Given two parsers `p` and `q` for type `a`, tries to parse with `p` and, if this fails,
tries to parse with `q`.
-}
(||) : {a: Type} -> Parser a -> Parser a -> Parser a
(||) p q l = (case (p l) of
                       (Success result rest) => Success result rest
                       Failed => q l)

-- recursive helper for `rep` method.
repParse: {a: Type} -> Parser a -> (inp: List Char) -> (accum: List a) -> ParseResult (List a)
repParse p inp accum = case (p inp) of
                            (Success result rest) => repParse p rest (result :: accum)
                            Failed => Success accum inp

-- helper for `rep` method
repRev : {a: Type} -> Parser a -> Parser (List a)
repRev p l =  repParse p l []

{- Given a parser `p`, returns a new parser that matches 0 or more
matches for `p` and returns a list of successful matches
-}
rep : {a: Type} -> Parser a -> Parser (List a)
rep p = map (repRev p) reverse

{- Given a parser `p`, returns a new parser that matches 1 or more
matches for `p` and returns a list of successful matches
-}
rep1 : {a: Type} -> Parser a -> Parser (List a)
rep1 p = map (p ++ (repRev p)) (\pair => (case pair of
                                            (a, b) => a:: reverse(b)))

-- Helper: given the  digits of a natural number from the list of digits from right to left
natFromRev : List Char -> Nat -> Nat
natFromRev [] n = 0
natFromRev (x :: xs) n =
  let
  d : Nat = n * cast( (ord x) - (ord '0'))
  in
  d + (natFromRev xs (10 * n))

-- Given the digits of a natural number, returns the number.
natFromChars : (List Char) -> Nat
natFromChars l = natFromRev (reverse l) 1

-- Parser to return a (literal) natural number, e.g. "231" -> 231
nat : Parser Nat
nat = map (rep1 (charPred isDigit)) (natFromChars)

-- Parser checking if al input is consumed.
eof : Parser Unit
eof [] = Success () []
eof (x :: xs) = Failed

-- Given a parser `p` for type `a` and a predicate
filter : {a: Type} -> Parser a -> (a -> Bool) -> Parser a
filter p pred l = case p l of
                       (Success result rest) =>
                         if pred result then Success result rest else Failed
                       Failed => Failed

infix 10 +>

-- Like (++) but drops the second matched term
(+>) : {a : Type} -> {b: Type} -> Parser a -> Parser b -> Parser a
(+>) p q l = (case p l of
                       (Success result1 rest1) => (case (q rest1) of
                                      (Success result2 rest2) => Success result1 rest2
                                      Failed => Failed)
                       Failed => Failed)

infix 11 <+

-- Like (++) but drops the first matched term
(<+) : {a : Type} -> {b: Type} -> Parser a -> Parser b -> Parser b
(<+) p q l = (case p l of
                      (Success result1 rest1) => (case (q rest1) of
                                      (Success result2 rest2) => Success result2 rest2
                                      Failed => Failed)
                      Failed => Failed)

{- Given a parser `p` for type `a` and a character `c`, matches for 1 or more
matches for `p` separated by `c`
-}
repSep: {a: Type} -> Parser a -> Char -> Parser (List a)
repSep p c =
  map((p +> (charLit c)) ++ (repSep p c))(
    \pair => (case pair of
          (x, ys) => x :: ys)) || map(p)(\n => n ::[])

{- Given a parser `p`, returns a parser that allows spaces before and after the match
-}
pad : {a: Type} -> Parser a -> Parser a
pad p =  rep(S " ") <+ p +> rep(S " ")

-- Parses a string with spaces allowed before and after
SS : String -> Parser String
SS s = pad (S s)

{- Given a parser `p` for type `a` and a character `c`, matches for 1 or more
matches for `p` separated by `c`, allowing spaces before and after `c`
-}
repSepTrim: {a: Type} -> Parser a -> Char -> Parser (List a)
repSepTrim p c =
  map((p +>  (pad(charLit c))) ++ (repSepTrim p c))(
    \pair => (case pair of
                    (x, ys) => x :: ys)) || map(p)(\n => n ::[])

{- The mutual block is a typical example of parsing: parsers for arithmetic
expressions involving + and * and parenthesis with the usual precedence,
calculating the resulting natural number
-}
mutual
  -- A simple term: a literal natural number or an expression in parenthesis
  simpleTerm : Parser Nat
  simpleTerm = nat || ( (SS "(") <+ expression +> (SS ")") )

  -- A product of simple terms, possibly with just one simple term
  term : Parser Nat
  term = map(repSepTrim simpleTerm '*')(foldl(*)(1))

  -- A sum of terms, possibly with just one term
  expression: Parser Nat
  expression = map(repSepTrim term '+')(foldl(+)(0))

{- Combining parsers to allow dependence on context. Concretely, given
  * A parser `p` for type `a`
  * A function `parsers` from `a` to parsers of type `b`
  We get a parser for type `b`. Namely, the parser `p` is applied to the input.
  If this succeeds with result `x: a`, the parser `q = parsers x` is applied to the
  rest of the input.
-}
flatMapWithNext : {a : Type} -> {b: Type} -> Parser a -> (a -> Parser b) -> Parser b
flatMapWithNext p parsers input =
  case p input of
          (Success result1 rest1) => (case (parsers result1) rest1 of
                    (Success result2 rest) => Success result2 rest
                    Failed => Failed)
          Failed => Failed

{- Given a parser `p` for type `a` and a function `f: a -> Maybe b` gives a parser for type `b`;
if `p` succeeds with result `x` and `f x = Just y`, then the parse is successful with result y;
all other cases fail
-}
mapMaybe : {a : Type} -> {b: Type} -> Parser a -> (a -> Maybe b) -> Parser b
mapMaybe p f s = case p s of
                      (Success result rest) =>
                        (case f result of
                              Nothing => Failed
                              (Just b) => Success b rest)
                      Failed => Failed

-- matches a letter
letter: Parser Char
letter = charPred (\x => 'a' <= x && x <= 'z')
