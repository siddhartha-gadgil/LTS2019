module Sort

Smaller : Nat -> Nat -> Nat
Smaller Z n = Z
Smaller  m Z = Z
Smaller  (S m) (S n) = (S (Smaller m n))

Min : (m: Nat) -> (n: Nat) -> Either (LTE m n) (LTE n m)
Min Z n = Left LTEZero
Min m Z = Right LTEZero
Min (S a) (S b) = case (Min a b) of
                       (Left l) => Left (LTESucc l)
                       (Right r) => Right (LTESucc r)

Insert: (n: Nat) -> List Nat -> List Nat
Insert n [] = [n]
Insert n (x :: xs) = case (Min n x) of
                        (Left l) => ([n] ++ [x]) ++ xs
                        (Right r) => [x] ++ (Insert n xs)


Sort: List Nat -> List Nat
Sort [] = []
Sort (x :: xs) = Insert x (Sort xs)
