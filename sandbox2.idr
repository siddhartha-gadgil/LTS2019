--Sandbox new

|||Proof of the type that an implication implies its contrapositive
impliesContrapositive : (a : Type) -> (b : Type) -> (a -> b) -> (b -> Void) -> (a -> Void)
impliesContrapositive a b proofAimpliesB proofBfalse x = proofBfalse (proofAimpliesB x)

functionExtendsEquality : (typ : Type) -> (f : typ -> typ) -> (n : typ) -> (m : typ) -> (n = m) -> (f n = f m)
functionExtendsEquality type f m m Refl = Refl

predNat : Nat -> Nat
predNat Z = Z
predNat (S k) = k

meqnSmeqSn : (m : Nat) -> (n : Nat) -> (S m = S n) -> (m = n)
meqnSmeqSn m n proofEq = functionExtendsEquality Nat predNat (S m) (S n) proofEq

ZIsNotS : {k : Nat} -> (Z = S k) -> Void
ZIsNotS Refl impossible

ltImpliesLTE : {a : Nat} -> {b : Nat} -> (LT a b) -> (LTE a b)
ltImpliesLTE proofLTE = lteSuccLeft proofLTE

eqImpliesLTE : {a : Nat} -> {b : Nat} -> (a = b) -> (LTE a b)
eqImpliesLTE {a = Z} {b = Z} Refl = LTEZero
eqImpliesLTE {a = S k} {b = Z} proofEq = void(SIsNotZ proofEq)
eqImpliesLTE {a = Z} {b = S l} proofEq = void(SIsNotZ (sym proofEq))
eqImpliesLTE {a = S k} {b = S l} proofEq = LTESucc (eqImpliesLTE (meqnSmeqSn k l proofEq))

lteRemoveConstantLeft : {a : Nat} -> {b : Nat} -> {c : Nat} -> (LTE (c + a) (c + b)) -> (LTE a b)
lteRemoveConstantLeft {a} {b} {c = Z} proofcplusaLTEcplusb = proofcplusaLTEcplusb
lteRemoveConstantLeft {a} {b} {c = S k} (LTESucc proofLTE) =
	lteRemoveConstantLeft {a} {b} {c = k} proofLTE

ltImpliesNotEqNotGT : {a : Nat} -> {b : Nat} -> (LT a b) -> (Not (a = b), Not (LT b a))
ltImpliesNotEqNotGT {a} {b = Z} proofLT = void(succNotLTEzero proofLT)
ltImpliesNotEqNotGT {a = Z} {b = S l} proofLT = (ZIsNotS, succNotLTEzero)
ltImpliesNotEqNotGT {a = S k} {b = S l} (LTESucc proofLT) =
	((impliesContrapositive (S k = S l) (k = l) (meqnSmeqSn k l) inductionStep1), (impliesContrapositive (LT (S l) (S k)) (LT l k) (lteRemoveConstantLeft {c = 1}) inductionStep2)) where
		inductionStep1 = fst (ltImpliesNotEqNotGT proofLT)
		inductionStep2 = snd (ltImpliesNotEqNotGT proofLT)

succNotLTEn : {n : Nat} -> (LT n n) -> Void
succNotLTEn {n = Z} proofLTE = void (succNotLTEzero proofLTE)
succNotLTEn {n = S k} (LTESucc proofLTE) =
	impliesContrapositive (LT (S k) (S k)) (LT k k) (lteRemoveConstantLeft {c = 1}) (succNotLTEn proofLTE)

eqimpliesNotLTNotGT : {a : Nat} -> {b : Nat} -> (a = b) -> (Not (LT a b), Not (LT b a))
eqimpliesNotLTNotGT {a = k} {b = k} Refl = (succNotLTEn, succNotLTEn)
