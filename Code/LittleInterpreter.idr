module LittleInterpreter

import LittleLang

-- This is not needed, plus does not work. We just use reduce in LittleLang.

-- Many cases commented out to appease typechecker
eqExp : (a: Ty) -> (b: Ty) -> Exp a -> Exp b -> Bool
eqExp NT NT (N k) (N l) = k == l
eqExp BT BT (B x) (B y) = x == y
eqExp NT b (N k) y = False
eqExp BT b (B x) y = False
eqExp BT BT (LTE x z) (LTE p q) = (eqExp NT NT x p) && (eqExp NT NT z q)
eqExp BT BT (EQ x z) (EQ p q)  = (eqExp NT NT x p) && (eqExp NT NT z q)
eqExp BT b (LTE x z) y = False
eqExp BT b (EQ x z) y = False
-- eqExp a b (If x z w) (If p q r) =
--   (eqExp BT BT x p) && (eqExp a b z q) && (eqExp a b w r)
-- eqExp a b (If x z w) y = False
-- eqExp a b (Var name a) (Var other b) = (name == other) && eqTyp a b
-- eqExp a b (Var name a) y = False
-- eqExp (FT domain codomain) (FT dd cc) (Lam var value) (Lam vr vl) =
--   (eqExp domain dd var vr) && (eqExp codomain cc value vl)
-- eqExp (FT domain codomain) b (Lam var value) y = False
-- eqExp a b (App x a f arg) (App y b g ar) =
--   (eqExp (FT x a) (FT y b) f g)
--   && (eqExp x y arg ar)
-- eqExp a b (App x a f arg) y = False
-- eqExp NT NT (Sum x z) (Sum p q) = (eqExp NT NT x p) && (eqExp NT NT z q)
-- eqExp NT NT (Pred x) (Pred y) = eqExp NT NT x y
-- eqExp NT a (Pred x) y = False
-- eqExp NT NT (Prod x z) (Prod p q) = (eqExp NT NT x p) && (eqExp NT NT z q)
-- eqExp NT b (Sum x z) y = False
-- eqExp NT b (Prod x z) y = False

interpret : (ctx: Context) -> (a: Ty) -> (exp : Exp a) -> Exp a
interpret ctx a exp =
  let next = simplify ctx a exp
  in
    if eqExp a a exp next then exp else interpret ctx a next
