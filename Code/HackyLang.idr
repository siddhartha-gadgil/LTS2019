module HackyLang
-- Warning: only briefly tested, may have bugs

-- An expression
data Exp : Type where
  N : Nat -> Exp -- a literal natural number
  B : Bool -> Exp -- a literal boolean
  LTE : Exp -> Exp -> Exp
  EQ : Exp -> Exp -> Exp
  If :  Exp -> Exp -> Exp -> Exp -- if expression
  Var : (name: String) -> Exp -- a variable
  Lam :  (var : Exp) -> (value : Exp) -> Exp -- a lambda expression
  App : (f : Exp ) -> (arg: Exp) -> Exp -- function application
  Sum :  Exp -> Exp -> Exp -- sum
  Prod: Exp -> Exp -> Exp  -- product
  Pred: Exp -> Exp -- predecessor of a natural number
  Null : Exp
  Cons: Exp -> Exp -> Exp
  Left: Exp -> Exp
  Right : Exp -> Exp

-- substitute `x` by `y` in `base`
subs:  (base: Exp) -> (x: Exp) -> (y: Exp) -> Exp
subs  (N k) x y = N k
subs  (B z) x y = B z
subs  (LTE z w) x y = LTE (subs z x y) (subs  w x y)
subs  (EQ z w) x y = EQ (subs  z x y) (subs  w x y)
subs (If z w s) x y =
  If (subs z x y) (subs w x y) (subs s x y)
subs (Var name) (Var other) y =
  if name == other
    then y
    else Var name
subs (Var name) x y = Var name
subs (Lam var value) x y =
  Lam (subs var x y) (subs value x y)
subs (App f arg) x y =
  App (subs f x y) (subs arg x y)
subs  (Sum z w) x y = Sum (subs  z x y) (subs  w x y)
subs  (Pred z) x y = Pred (subs   z x y)
subs  (Prod z w) x y = Prod (subs  z x y) (subs w x y)
subs Null x y = Null
subs (Left a) x y = Left (subs a x y)
subs (Right a) x y = Right (subs a x y)
subs (Cons a b) x y = Cons (subs a x y) (subs b x y)

data Defn : Type where
  Let : (name: String) -> (value: Exp) -> Defn

-- A list of definitions of variables
Context : Type
Context = List Defn

varValue: Context -> (name: String) -> Maybe (Exp)
varValue [] name = Nothing
varValue ((Let x value) :: xs) name =
  if x == name then Just value else Nothing

{-
Simplify an expression in context by one step if possible. The simplifications are:
  * if an expression is a variable defined in the context, it is replaced by its value
  * sums, products and predecessors of _literals_ are simplifed, e.g. `Sum (N 2) (N 3)` becomes `N 5`
  * a lambda function `x :-> y` applied to `z` simplifies to the result of subtituting `x` by `z` in `y`.
  * for any other composite term, we simplify the components.
-}
simplify : (ctx: Context) -> (exp : Exp) -> Exp
simplify ctx  (N k) = N k
simplify ctx  (B x) = B x
simplify ctx  Null = Null
simplify ctx  (LTE (N x) (N y)) = B (x <= y)
simplify ctx  (LTE x y) = LTE (simplify ctx  x) (simplify ctx  y)
simplify ctx  (EQ (N x) (N y)) = B (x == y)
simplify ctx  (EQ (B x) (B y)) = B (x == y)
simplify ctx  (EQ Null Null) = B True
simplify ctx  (EQ Null (N _)) = B False
simplify ctx  (EQ Null (B _)) = B False
simplify ctx  (EQ Null (Cons _ _)) = B False
simplify ctx  (EQ (N _) Null) = B False
simplify ctx  (EQ (B _) Null) = B False
simplify ctx  (EQ (Cons _ _) Null) = B False
simplify ctx  (EQ (B _) (N _)) = B False
simplify ctx  (EQ (N _) (B _)) = B False
simplify ctx  (EQ x y) = EQ (simplify ctx  x) (simplify ctx  y)
simplify ctx (If (B True) y z) = y
simplify ctx  (If (B False) y z) = z
simplify ctx  (If x y z) = If (simplify ctx x) (simplify ctx  y) (simplify ctx  z)
simplify ctx  (Var name) = (case varValue ctx name of
                              Nothing => Var name
                              (Just x) => x)
simplify ctx (Lam var value) = Lam var value
simplify ctx (App (Lam var value) arg) = subs value var arg
simplify ctx (App f arg) = App (simplify ctx f) (simplify ctx arg)
simplify ctx  (Sum (N x) (N y)) = N (x + y)
simplify ctx  (Sum x y) = Sum (simplify ctx  x) (simplify ctx  y)
simplify ctx  (Pred (N x)) = N (pred x)
simplify ctx  (Pred x) = Pred (simplify ctx  x)
simplify ctx  (Prod (N x) (N y)) = N (x * y)
simplify ctx  (Prod x y) = Prod (simplify ctx  x) (simplify ctx  y)
simplify ctx (Left (Cons a b)) = a
simplify ctx (Right (Cons a b)) = b
simplify ctx (Left a) = Left (simplify ctx a)
simplify ctx (Right a) = Right (simplify ctx a)
simplify ctx (Cons a b) = Cons (simplify ctx a) (simplify ctx b)


data Program: Type where
  Code: (context: Context) -> (main: Exp) -> Program

-- repeatedly simplify an expression till we get a literal natural (or loop forever)
getNat : Context -> Exp -> Nat
getNat ctx exp = case (simplify ctx  exp) of
                  (N k) => k
                  x => getNat ctx x

steps: Context -> Exp -> Nat -> Exp
steps x y Z = y
steps x y (S k) = simplify x (steps x y k)

run: Program -> Exp -> Nat
run (Code context main) exp = getNat context (App main exp)

-- An example
not: Exp
not = Lam (Var "x" ) (If (Var "x" ) (B False) (B True))

-- a variable
n: Exp
n = Var "n"

-- a variable for the factorial function
fac : Exp
fac = Var "fac"

-- the expression `fac(n - 1)`
prev: Exp
prev = Prod (App fac (Pred n)) n

-- the expression `if n == 0 then 1 else fac(n-1)`
rhs : Exp
rhs = If (EQ n (N Z)) (N 1) prev

{- the context with definition:
  fac := n :-> (if (n == 0) then 1 else fac(n - 1)
-}
ctx: Context
ctx = (Let "fac" (Lam n rhs)) :: []

-- function computing factorial
facFn: Nat -> Nat
facFn n = getNat ctx (App fac (N n))

facProg: Program
facProg = Code ctx fac


--- Another program, summing lists
sm: Exp
sm = Var "sum"

l: Exp
l = Var "l"

sid: Exp
sid = If (EQ Null l) (N 0) (Sum (Left l) (App sm (Right l)))

sctx : Context
sctx = (Let "sum" (Lam l sid)) :: []

sumProg: Program
sumProg = Code sctx sm

egList: Exp
egList = Cons (N 5) (Cons (N 3) (Cons (N 4) Null ))
--- Run `run sumProg egList` to see lists being added
