module Parsers

%access public export

data ParseResult : Type -> Type where
  ParseSuccess : {a: Type} -> (result : a) -> (rest: List Char) -> ParseResult a
  ParseFailed : {a: Type} -> (rest: List Char) -> ParseResult a

Parser: Type -> Type
Parser a = (List Char) -> ParseResult a

parseChars : {a: Type} -> Parser a -> List Char -> ParseResult a
parseChars  p xs = p xs

parse : {a: Type} -> Parser a -> String -> ParseResult a
parse p s = parseChars p (unpack s)


charPred : (Char -> Bool) -> Parser Char
charPred p l = (case l of
                     [] => ParseFailed  ([])
                     (x :: xs) =>
                       if (p x) then (ParseSuccess x xs) else ParseFailed (x :: xs))

charLit : Char -> Parser Char
charLit c = charPred (\x => x == c)

map : {a: Type} -> {b: Type} -> Parser a -> (a -> b) -> Parser b
map p f cs = (case (p cs) of
                           (ParseSuccess  result rest) => ParseSuccess  (f result) rest
                           (ParseFailed  rest) => ParseFailed  rest)

(++) : {a : Type} -> {b: Type} -> Parser a -> Parser b -> Parser (Pair a b)
(++) p q l = (case p l of
                       (ParseSuccess result1 rest1) => (case (q rest1) of
                                                           (ParseSuccess result2 rest2) => ParseSuccess ((result1, result2)) rest2
                                                           (ParseFailed rest2) => ParseFailed l)
                       (ParseFailed rest) => ParseFailed rest)

-- charsLit: (List Char) -> Parser (List Char)
-- charsLit cs  l = case cs of
--                    [] =>  ParseSuccess [] l
--                    (x :: xs) =>
--                     let
--                     h = charLit x
--                     t = charsLit xs
--                     in
--                     map (h ++ t) (\pair => (case pair of
--                                                  (a, b) => a :: b))


charsLit: (List Char) -> Parser (List Char)
charsLit []  l = ParseSuccess [] l
charsLit (x :: xs) [] = ParseFailed []
charsLit (x :: xs) (a :: bs) =
                  (case charLit x (a :: bs) of
                        (ParseSuccess result1 rest) => (case (charsLit xs bs) of
                                                             (ParseSuccess result2 rest) => ParseSuccess (result1 :: result2) rest
                                                             (ParseFailed rest) => ParseFailed (a :: bs))
                        (ParseFailed rest) => ParseFailed rest)



S: String -> Parser String
S s = map (charsLit (unpack s)) pack

(||) : {a: Type} -> Parser a -> Parser a -> Parser a
(||) p q l = (case (p l) of
                       (ParseSuccess result rest) => ParseSuccess result rest
                       (ParseFailed rest) => q rest)

repParse: {a: Type} -> Parser a -> (inp: List Char) -> (accum: List a) -> ParseResult (List a)
repParse p inp accum = case (p inp) of
                            (ParseSuccess result rest) => repParse p rest (result :: accum)
                            (ParseFailed rest) => ParseSuccess accum inp

repRev : {a: Type} -> Parser a -> Parser (List a)
repRev p l =  repParse p l []

rep : {a: Type} -> Parser a -> Parser (List a)
rep p = map (repRev p) reverse

rep1 : {a: Type} -> Parser a -> Parser (List a)
rep1 p = map (p ++ (repRev p)) (\pair => (case pair of
                                            (a, b) => a:: reverse(b)))
natFromRev : List Char -> Nat -> Nat
natFromRev [] n = 0
natFromRev (x :: xs) n =
  let
  d : Nat = n * cast( (ord x) - (ord '0'))
  in
  d + (natFromRev xs (10 * n))

natFromChars : (List Char) -> Nat
natFromChars l = natFromRev (reverse l) 1

nat : Parser Nat
nat = map (rep1 (charPred isDigit)) (natFromChars)

eof : Parser Unit
eof [] = ParseSuccess () []
eof (x :: xs) = ParseFailed (x :: xs)

plusNat : Parser Nat
plusNat = map ((S "+") ++ nat)(\pair => (case pair of
                                              (a, b) => b))

sumExpr: Parser ((Nat, List Nat))
sumExpr = nat ++ (rep plusNat)

sumVal: (Nat, List Nat) -> Nat
sumVal (a, b) = foldl((+))(a)(b)

sum: Parser Nat
sum = map(sumExpr)(sumVal)

infix 10 +>

(+>) : {a : Type} -> {b: Type} -> Parser a -> Parser b -> Parser a
(+>) p q l = (case p l of
                       (ParseSuccess result1 rest1) => (case (q rest1) of
                                                           (ParseSuccess result2 rest2) => ParseSuccess result1 rest2
                                                           (ParseFailed rest2) => ParseFailed l)
                       (ParseFailed rest) => ParseFailed rest)

infix 11 <+

(<+) : {a : Type} -> {b: Type} -> Parser a -> Parser b -> Parser b
(<+) p q l = (case p l of
                      (ParseSuccess result1 rest1) => (case (q rest1) of
                                                          (ParseSuccess result2 rest2) => ParseSuccess result2 rest2
                                                          (ParseFailed rest2) => ParseFailed l)
                      (ParseFailed rest) => ParseFailed rest)

repSep: {a: Type} -> Parser a -> Char -> Parser (List a)
repSep p c = map((p +> (charLit c)) ++ (repSep p c))(\pair => (case pair of
                                                        (x, ys) => x :: ys)) || map(p)(\n => n ::[])

pad : {a: Type} -> Parser a -> Parser a
pad p =  rep(S " ") <+ p +> rep(S " ")

SS : String -> Parser String
SS s = pad (S s)

repSepTrim: {a: Type} -> Parser a -> Char -> Parser (List a)
repSepTrim p c = map((p +>  (pad(charLit c))) ++ (repSepTrim p c))(\pair => (case pair of
                                                        (x, ys) => x :: ys)) || map(p)(\n => n ::[])


mutual
  simpleTerm : Parser Nat
  simpleTerm = nat || ( (SS "(") <+ expression +> (SS ")") )

  term : Parser Nat
  term = map(repSepTrim simpleTerm '*')(foldl(*)(1))

  expression: Parser Nat
  expression = map(repSepTrim term '+')(foldl(+)(0))


flatMapWithNext : {a : Type} -> {b: Type} -> Parser a -> (a -> Parser b) -> Parser b
flatMapWithNext p f s = case p s of
                             (ParseSuccess result rest) => (f result) rest
                             (ParseFailed rest) => ParseFailed s

mapMaybe : {a : Type} -> {b: Type} -> Parser a -> (a -> Maybe b) -> Parser b
mapMaybe p f s = case p s of
                      (ParseSuccess result rest) =>
                        (case f result of
                              Nothing => ParseFailed s
                              (Just b) => ParseSuccess b rest)
                      (ParseFailed rest) => ParseFailed rest

letter: Parser Char
letter = charPred (\x => 'a' <= x && x <= 'z')
