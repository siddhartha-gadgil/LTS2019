module Scheme_Parsers

%access public export

||| The type of outputs of a parsing
data ParseResult : Type -> Type where
  Success : {a: Type} -> (result : a) -> (rest: List Char) -> ParseResult a
  Failed : {a: Type} -> (rest: List Char) -> ParseResult a
  
||| The type of parsers  
Parser: Type -> Type
Parser a = (List Char) -> ParseResult a  

||| Convenience method to apply a parser to a input
parseChars : {a: Type} -> Parser a -> List Char -> ParseResult a
parseChars p xs = p xs

||| Convenience method to parse strings instead of lists of characters 
parse : {a: Type} -> Parser a -> String -> ParseResult a
parse p s = parseChars p (unpack s)

||| Method to decide if something is true about the character. Will be used mostly
||| to decide if it is equal to some specific character.
charPred : (Char -> Bool) -> Parser Char
charPred p l = (case l of
    [] => Failed  ([])
    (x :: xs) =>
        if (p x) then (Success x xs) else Failed (x :: xs))

||| Given a character gives the function to check if another character is equal to it                       
charLit : Char -> Parser Char
charLit c = charPred (\x => x == c)                       

||| Given a function (A -> B) and a parser of type A gives a Parser of type B.
map : {a: Type} -> {b: Type} -> Parser a -> (a -> b) -> Parser b
map p f cs = (case (p cs) of
    (Success  result rest) => Success  (f result) rest
    (Failed  rest) => Failed  rest)

||| Given two parser p and q applies p to l. If succeeds apllies q to the rest and outputs the combined result                           
(++) : {a : Type} -> {b: Type} -> Parser a -> Parser b -> Parser (Pair a b)
(++) p q l = (case p l of
    (Success result1 rest1) => (case (q rest1) of
        (Success result2 rest2) => Success ((result1, result2)) rest2
        (Failed rest2) => Failed l)
    (Failed rest) => Failed rest)
    
||| Matches a list of characters A to another list of characters B. If A is the beginning of B succeeds.
charsLit: (List Char) -> Parser (List Char)
charsLit []  l = Success [] l
charsLit (x :: xs) [] = Failed []
charsLit (x :: xs) (a :: bs) =
    (case charLit x (a :: bs) of
        (Success result1 rest) => (case (charsLit xs bs) of
            (Success result2 rest) => Success (result1 :: result2) rest
            (Failed rest) => Failed (a :: bs))
        (Failed rest) => Failed rest)  
        
||| Uses charLit to match a string. Also gives strings as output.  
S: String -> Parser String
S s = map (charsLit (unpack s)) pack 

||| Given to parsers p and q applies p to input. If succeeds then outputs the result. If fails applies 
||| q to the result and outputs the result.

(||) : {a: Type} -> Parser a -> Parser a -> Parser a
(||) p q l = (case (p l) of
                       (Success result rest) => Success result rest
                       (Failed rest) => q rest)                                    

||| Helper method to repeatedly apply a Parser.                            
repParse: {a: Type} -> Parser a -> (inp: List Char) -> (accum: List a) -> ParseResult (List a)
repParse p inp accum = case (p inp) of
                            (Success result rest) => repParse p rest (result :: accum)
                            (Failed rest) => Success accum inp                           

||| Gives a Parser for a list of type A given a Parser of type A.                           
repRev : {a: Type} -> Parser a -> Parser (List a)
repRev p l =  repParse p l [] 

||| Applies the Parser zero or more times and outputs the result in reverse. Notice that due to
||| Structure of the List the output of repRev is actually the reverse of what we want.
rep : {a: Type} -> Parser a -> Parser (List a)
rep p = map (repRev p) reverse   

||| Same as rep except it runs the Parser for one or more times, so that it does not take empty
||| inputs as valid ones
rep1 : {a: Type} -> Parser a -> Parser (List a)
rep1 p = map (p ++ (repRev p)) (\pair => (case pair of
                                            (a, b) => a :: reverse(b)))                       

||| Helper method to get the natural number from the corresponding reversed list of characters.                           
natFromRev : List Char -> Double -> Double
natFromRev [] n = 0
natFromRev (x :: xs) n =
  let
  d : Double = n * (cast ( (ord x) - (ord '0')))
  in
  d + (natFromRev xs (10 * n))                           
                           
||| Helper method to get the number after the decimal
floatFromCharHelper : List Char -> (exp : Double) -> (accum : Double) -> Double
floatFromCharHelper [] n accum = accum
floatFromCharHelper (x :: xs) n accum = 
    let
    d : Double = n * (cast ( (ord x) - (ord '0') ))
    in
    (floatFromCharHelper xs (n * 0.1) (d + accum))                         
                           
||| Method to get the number after the decimal
floatAfterDecimal : List Char -> Double
floatAfterDecimal l = (floatFromCharHelper l 0.1 0) 

||| Method to get the number corresponding to the list of characters
natFromChars : (List Char) -> Double
natFromChars l = natFromRev (reverse l) 1                          

||| Checks if there is a natural number in the beginning of the list of characters. And outputs
||| the result, which is the maximum consumable input along with the unconsumed part
nat : Parser Double
nat = map (rep1 (charPred isDigit)) (natFromChars)  

||| Gives the float assuming it is after the decimal point. It does not accept non zero inputs 
floatAfter : Parser Double
floatAfter = map (rep1 (charPred isDigit)) (floatAfterDecimal)

||| Checks if the character is equal to '.'
isDot : Char -> Bool
isDot a = a == '.'

||| Helper method to get the number from the string
floatFromCharHelper1 : List Char -> ParseResult Double
floatFromCharHelper1 [] = Failed []
floatFromCharHelper1 (x :: xs) = case (isDot x) of
    True => (floatAfter xs)
    False => Failed (x :: xs)
    
||| Gets the double from the string. Note that input has to be of the form "a.b" where both a and
||| b are non empty strings of characters 0 - 9
float : Parser Double
float expr = case (nat expr) of
    (Success before rest) => case (floatFromCharHelper1 rest) of
        (Success after rest) => Success (before + after) rest
        (Failed rest) => Failed expr  
    (Failed rest) => (Failed rest)








                         
                           
                           
                           
                           
                           
                           

