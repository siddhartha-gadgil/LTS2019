module LittleLang

public export
data Ty : Type where
  NT : Ty
  BT : Ty
  FT : Ty -> Ty -> Ty

public export
data Exp : Ty -> Type where
  N : Nat -> Exp NT
  B : Bool -> Exp BT
  LTE : Exp NT -> Exp NT -> Exp BT
  EQ : Exp NT -> Exp NT -> Exp BT
  If : {a: Ty} ->  Exp BT -> Exp a -> Exp a -> Exp a
  Var : (name: String) -> (type: Ty) -> Exp type
  Lam : {domain: Ty} -> {codomain: Ty} -> (var : Exp domain)   -> (value : Exp codomain) -> Exp (FT domain codomain)
  App : (a: Ty) -> (b: Ty)  -> (f : Exp (FT a b)) -> (arg: Exp a) -> Exp b
  Sum :  Exp NT -> Exp NT -> Exp NT
  Prod: Exp NT -> Exp NT -> Exp NT
  Pred: Exp NT -> Exp NT

not: Exp (FT BT BT)
not = Lam (Var "x" BT) (If (Var "x" BT) (B False) (B True))

mapTyp : (a : Ty) -> (b: Ty) -> Exp a -> Maybe (Exp b)
mapTyp NT NT x = Just x
mapTyp NT BT x = Nothing
mapTyp NT (FT y z) x = Nothing
mapTyp BT NT x = Nothing
mapTyp BT BT x = Just x
mapTyp BT (FT y z) x = Nothing
mapTyp (FT y z) NT x = Nothing
mapTyp (FT y z) BT x = Nothing
mapTyp (FT y z) (FT w s) (If x t u) =
  case (mapTyp (FT y z) (FT w s) t) of
    Nothing => Nothing
    (Just q) => (case (mapTyp (FT y z) (FT w s) u) of
         Nothing => Nothing
         (Just p) => Just (If x q p))
mapTyp (FT y z) (FT w s) (Var name (FT y z)) =
  if (isJust (mapTyp y w (Var name y))) && (isJust (mapTyp z s (Var name z)))
    then Just(Var name (FT w s)) else Nothing
mapTyp (FT y z) (FT w s) (Lam var value) =
  case (mapTyp y w var) of
      Nothing => Nothing
      (Just x) => (case (mapTyp z s value) of
                        Nothing => Nothing
                        (Just p) => Just (Lam x p))
mapTyp (FT y z) (FT w s) (App a (FT y z) f arg) =
  (case mapTyp (FT a (FT y z)) (FT a (FT w s)) f of
        Nothing => Nothing
        (Just g) =>
          Just(App a (FT w s) g arg)
        )

export
eqTyp : Ty -> Ty -> Bool
eqTyp x y = isJust (mapTyp x y (Var "test" x))


subs: (a: Ty) -> (b: Ty) -> (base: Exp a) -> (x: Exp b) -> (y: Exp b) -> Exp a
subs NT b (N k) x y = N k
subs BT b (B z) x y = B z
subs BT b (LTE z w) x y = LTE (subs NT b z x y) (subs NT b w x y)
subs BT b (EQ z w) x y = EQ (subs NT b z x y) (subs NT b w x y)
subs a b (If z w s) x y =
  If (subs _ _ z x y) (subs _ _ w x y) (subs _ _ s x y)
subs a b (Var name a) (Var other b) y =
  if name == other
    then (case mapTyp b a y of
               Nothing => Var name a
               (Just x) => x)
    else Var name a
subs a b (Var name a) x y = Var name a
subs (FT domain codomain) b (Lam var value) x y =
  Lam (subs domain b var x y) (subs codomain b value x y)
subs a b (App c a f arg) x y =
  App c a (subs _ _ f x y) (subs c b arg x y)
subs NT b (Sum z w) x y = Sum (subs NT b z x y) (subs NT b w x y)
subs NT b (Pred z) x y = Pred (subs NT b z x y)
subs NT b (Prod z w) x y = Prod (subs NT b z x y) (subs NT b w x y)

public export
data Context : Type where
  Empty: Context
  Cons : (name: String) -> (type: Ty) -> (value: Exp type) -> (tail: Context) -> Context

varValue: Context -> (name: String) -> (ty: Ty) -> Maybe (Exp ty)
varValue Empty name ty = Nothing
varValue (Cons x type value tail) name ty =
  if (x==name)
    then (case mapTyp type ty value of
               Nothing => Nothing
               (Just x) => Just x)
    else Nothing

export
simplify : (ctx: Context) -> (a: Ty) -> (exp : Exp a) -> Exp a
simplify ctx NT (N k) = N k
simplify ctx BT (B x) = B x
simplify ctx BT (LTE (N x) (N y)) = B (x <= y)
simplify ctx BT (LTE x y) = LTE (simplify ctx NT x) (simplify ctx NT y)
simplify ctx BT (EQ (N x) (N y)) = B (x == y)
simplify ctx BT (EQ x y) = EQ (simplify ctx NT x) (simplify ctx NT y)
simplify ctx a (If (B True) y z) = y
simplify ctx a (If (B False) y z) = z
simplify ctx a (If x y z) = If (simplify ctx _ x) (simplify ctx _ y) (simplify ctx _ z)
simplify ctx a (Var name a) =
  (case varValue ctx name a of
        Nothing => Var name a
        (Just x) => x)
simplify ctx (FT domain codomain) (Lam var value) = Lam var value
simplify ctx a (App x a (Lam var value) arg) = subs _ _ value var arg
simplify ctx a (App x a f arg) = App x a (simplify ctx _ f) (simplify ctx _ arg)
simplify ctx NT (Sum (N x) (N y)) = N (x + y)
simplify ctx NT (Sum x y) = Sum (simplify ctx NT x) (simplify ctx NT y)
simplify ctx NT (Pred (N x)) = N (pred x)
simplify ctx NT (Pred x) = Pred (simplify ctx NT x)
simplify ctx NT (Prod (N x) (N y)) = N (x * y)
simplify ctx NT (Prod x y) = Prod (simplify ctx NT x) (simplify ctx NT y)

reduce : Context -> Exp NT -> Nat
reduce ctx exp = case (simplify ctx NT exp) of
                  (N k) => k
                  x => reduce ctx x

n: Exp NT
n = Var "n" NT

fac : Exp (FT NT NT)
fac = Var "fac" (FT NT NT)

prev: Exp NT
prev = Prod (App NT NT fac (Pred n)) n

rhs : Exp NT
rhs = If (EQ n (N Z)) (N 1) prev

ctx: Context
ctx = Cons "fac" (FT NT NT) (Lam n rhs) Empty

facFn: Nat -> Nat
facFn n = reduce ctx (App NT NT fac (N n))
