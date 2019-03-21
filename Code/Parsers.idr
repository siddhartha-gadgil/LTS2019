module Parsers

%access public export

data ParseResult : Type -> Type where
  Success : {a: Type} -> (result : a) -> (rest: List Char) -> ParseResult a
  Failed : {a: Type} -> (rest: List Char) -> ParseResult a

Parser: Type -> Type
Parser a = (List Char) -> ParseResult a

parseChars : {a: Type} -> Parser a -> List Char -> ParseResult a
parseChars  p xs = p xs

parse : {a: Type} -> Parser a -> String -> ParseResult a
parse p s = parseChars p (unpack s)


charPred : (Char -> Bool) -> Parser Char
charPred p l = (case l of
                     [] => Failed  ([])
                     (x :: xs) =>
                       if (p x) then (Success x xs) else Failed (x :: xs))

charLit : Char -> Parser Char
charLit c = charPred (\x => x == c)

map : {a: Type} -> {b: Type} -> Parser a -> (a -> b) -> Parser b
map p f cs = (case (p cs) of
                           (Success  result rest) => Success  (f result) rest
                           (Failed  rest) => Failed  rest)

(++) : {a : Type} -> {b: Type} -> Parser a -> Parser b -> Parser (Pair a b)
(++) p q l = (case p l of
                       (Success result1 rest1) =>
                          (case (q rest1) of
                              (Success result2 rest2) => Success ((result1, result2)) rest2
                              (Failed rest2) => Failed l)
                       (Failed rest) => Failed rest)


charsLit: (List Char) -> Parser (List Char)
charsLit []  l = Success [] l
charsLit (x :: xs) [] = Failed []
charsLit (x :: xs) (a :: bs) =
                  (case charLit x (a :: bs) of
                        (Success result1 rest) => (case (charsLit xs bs) of
                                (Success result2 rest) => Success (result1 :: result2) rest
                                (Failed rest) => Failed (a :: bs))
                        (Failed rest) => Failed rest)



S: String -> Parser String
S s = map (charsLit (unpack s)) pack

(||) : {a: Type} -> Parser a -> Parser a -> Parser a
(||) p q l = (case (p l) of
                       (Success result rest) => Success result rest
                       (Failed rest) => q rest)

repParse: {a: Type} -> Parser a -> (inp: List Char) -> (accum: List a) -> ParseResult (List a)
repParse p inp accum = case (p inp) of
                            (Success result rest) => repParse p rest (result :: accum)
                            (Failed rest) => Success accum inp

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
eof [] = Success () []
eof (x :: xs) = Failed (x :: xs)

filter : {a: Type} -> Parser a -> (a -> Bool) -> Parser a
filter p pred l = case p l of
                       (Success result rest) =>
                         if pred result then Success result rest else Failed l
                       (Failed rest) => Failed rest

infix 10 +>

(+>) : {a : Type} -> {b: Type} -> Parser a -> Parser b -> Parser a
(+>) p q l = (case p l of
                       (Success result1 rest1) => (case (q rest1) of
                                      (Success result2 rest2) => Success result1 rest2
                                      (Failed rest2) => Failed l)
                       (Failed rest) => Failed rest)

infix 11 <+

(<+) : {a : Type} -> {b: Type} -> Parser a -> Parser b -> Parser b
(<+) p q l = (case p l of
                      (Success result1 rest1) => (case (q rest1) of
                                      (Success result2 rest2) => Success result2 rest2
                                      (Failed rest2) => Failed l)
                      (Failed rest) => Failed rest)

repSep: {a: Type} -> Parser a -> Char -> Parser (List a)
repSep p c =
  map((p +> (charLit c)) ++ (repSep p c))(
    \pair => (case pair of
          (x, ys) => x :: ys)) || map(p)(\n => n ::[])

pad : {a: Type} -> Parser a -> Parser a
pad p =  rep(S " ") <+ p +> rep(S " ")

SS : String -> Parser String
SS s = pad (S s)

repSepTrim: {a: Type} -> Parser a -> Char -> Parser (List a)
repSepTrim p c =
  map((p +>  (pad(charLit c))) ++ (repSepTrim p c))(
    \pair => (case pair of
                    (x, ys) => x :: ys)) || map(p)(\n => n ::[])


mutual
  simpleTerm : Parser Nat
  simpleTerm = nat || ( (SS "(") <+ expression +> (SS ")") )

  term : Parser Nat
  term = map(repSepTrim simpleTerm '*')(foldl(*)(1))

  expression: Parser Nat
  expression = map(repSepTrim term '+')(foldl(+)(0))


flatMapWithNext : {a : Type} -> {b: Type} -> Parser a -> (a -> Parser b) -> Parser b
flatMapWithNext p parsers input =
  case p input of
          (Success result1 rest1) => (case (parsers result1) rest1 of
                    (Success result2 rest) => Success result2 rest
                    (Failed rest) => Failed input)
          (Failed rest) => Failed rest

mapMaybe : {a : Type} -> {b: Type} -> Parser a -> (a -> Maybe b) -> Parser b
mapMaybe p f s = case p s of
                      (Success result rest) =>
                        (case f result of
                              Nothing => Failed s
                              (Just b) => Success b rest)
                      (Failed rest) => Failed rest

letter: Parser Char
letter = charPred (\x => 'a' <= x && x <= 'z')
