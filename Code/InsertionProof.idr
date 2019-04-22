module InsertionProof

import Data.Vect
import congruence
import Data.Fin
import Permutation
import PermCons
import Finite
import DecOrderNat
import LTE_Properties
import SortingWithProof
import InsertionSort
import InsertionHelpers
import PermConsProperties

%access public export
%default total

insertProof : (n : Nat) -> (a : Nat) -> (xs : (Vect n Nat)) ->
              (SortedVect n xs) -> (SortedVect (S n) (a :: xs))

insertProof Z a Nil sorted_Nil =
    ( [a] ** ((Idt (S Z) ** (Refl, (insertHelper8 a)))))

insertProof (S Z) a [x] sorted_x = case (decMin a x) of
    (Left pfLTE) => let
        pf = insertHelper8 x
        in
        ( [a, x] ** ((Idt 2) ** (Refl, (insertHelper1 Z a x Nil pfLTE pf))))
    (Right pfLTE) => let
        pf = insertHelper8 a
        in
        ( [x, a] ** ((Swap 2 FZ) ** (Refl, (insertHelper1 Z x a Nil pfLTE pf))))

insertProof (S (S n)) a xs sorted_xs = let
    {-
    (x :: u) = (fst sorted_xs)
    perm_xs = (fst (snd sorted_xs))
    pf_total_xs = (snd (snd sorted_xs))
    pf_perm_xs = fst pf_total_xs  -- perm_xs xs = (x :: u)
    pf_sorted_xs = snd pf_total_xs

    in

    case (decMin a (head (fst sorted_xs))) of

        (Left pfLTE) => let

            perm = includePerm (S (S n)) (fst (snd sorted_xs)) -- perm_xs as a permutation of a :: xs

            pf1_1 = PermC_prp_1 (S (S n)) a xs (fst (snd sorted_xs))
            -- ( (a :: (applyPerm n Nat perm xs)) = (applyPerm (S n) Nat (includePerm n perm) (a :: xs)))

            pf1_2 = congruence (Vect (S (S n)) Nat) (Vect (S (S (S n))) Nat)
                (fst sorted_xs) (applyPerm (S (S n)) Nat (fst (snd sorted_xs)) xs)
                (\k => (a :: k)) (sym pf_perm_xs)
            -- a :: fst sorted_xs = a :: applyPerm (S (S n)) Nat (fst (snd sorted_xs)) xs


            pf1_3 = sym (trans pf1_2 pf1_1)
            -- applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs) = a :: fst sorted_xs

            pf1_5 = (\k => (insertHelper10 (S n) (fst sorted_xs) k (pf_sorted_xs k)))

            pf1_4 = insertHelper1 (S n) a (head (fst sorted_xs)) (tail (fst sorted_xs)) pfLTE pf1_5

            in
            ((a :: (fst sorted_xs)) ** (perm ** (pf1_3, ?rhs)))

        (Right pfLTE) => ?rhs2
      -}

    (x1 :: v1) = (fst sorted_xs)
    x = (head (fst sorted_xs))
    u = (tail (fst sorted_xs))
    perm_xs = (fst (snd sorted_xs))
    pf_total_xs = (snd (snd sorted_xs))
    pf_perm_xs = fst pf_total_xs  -- perm_xs xs = v
    pf_sorted_xs = snd pf_total_xs
    pf1_5 = (\k => (insertHelper10 (S n) (fst sorted_xs) k (pf_sorted_xs k)))

    -- IsSorted (S (S n)) (head (fst sorted_xs) :: tail (fst sorted_xs)) :=

    --  (k16 : Fin (S (S n))) ->
    --      LTE (index (Data.Fin.Fin (S n) implementation of Prelude.Enum, method pred k16)
    --          (head (fst sorted_xs) :: tail (fst sorted_xs)))
    --              (index k16 (head (fst sorted_xs) :: tail (fst sorted_xs)))

    in

    case (decMin a (head (fst sorted_xs))) of

        (Left pfLTE) =>
        let
            perm = includePerm (S (S n)) (fst (snd sorted_xs))

            pf1_1 = PermC_prp_1 (S (S n)) a xs (fst (snd sorted_xs))
            -- a :: applyPerm (S (S n)) Nat (fst (snd sorted_xs)) xs =
            --    applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs)

            pf1_2 = congruence (Vect (S (S n)) Nat) (Vect (S (S (S n))) Nat)
                (fst sorted_xs) (applyPerm (S (S n)) Nat (fst (snd sorted_xs)) xs)
                (\k => (a :: k)) (sym pf_perm_xs)
            -- a :: fst sorted_xs = a :: applyPerm (S (S n)) Nat (fst (snd sorted_xs)) xs

            pf1_3 = sym (trans pf1_2 pf1_1)
            -- applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs) = a :: fst sorted_xs

            pf1_4 = insertHelper1 (S n) a (head (fst sorted_xs)) (tail (fst sorted_xs)) pfLTE pf1_5 --pf_sorted_xs

            -- IsSorted (S (S (S n))) (a :: (head (fst sorted_xs) :: tail (fst sorted_xs))) :=

            --(k : Fin (S (S (S n)))) ->
            --    LTE (index (Data.Fin.Fin (S n) implementation of Prelude.Enum, method pred k)
            --        (a :: head (fst sorted_xs) :: tail (fst sorted_xs)))
            --            (index k (a :: head (fst sorted_xs) :: tail (fst sorted_xs)))

            pf1_7 = vect_prp1 (S n) (fst sorted_xs)
            -- fst sorted_xs = head (fst sorted_xs) :: tail (fst sorted_xs)


            pf1_8 = congruence (Vect (S (S n)) Nat) (Vect (S (S (S n))) Nat) (fst sorted_xs)
                ((head (fst sorted_xs)) :: (tail (fst sorted_xs))) (\k => (a :: k)) pf1_7
            -- a :: fst sorted_xs = a :: head (fst sorted_xs) :: tail (fst sorted_xs)

            pf1_6 = insertHelper11 (S (S n)) (a :: head (fst sorted_xs) :: tail (fst sorted_xs))
                (a :: (fst sorted_xs)) (sym pf1_8) pf1_4
            -- IsSorted (S (S (S n))) (a :: (fst sorted_xs)) :=

            --(k : Fin (S (S (S n)))) ->
            --    LTE (index (Data.Fin.Fin (S n) implementation of Prelude.Enum, method pred k) (a :: fst sorted_xs))
            --        (index k (a :: fst sorted_xs))


            in
            ( (a :: (fst sorted_xs)) ** (perm ** (pf1_3, pf1_6)))


        (Right pfLTE) =>

        let

            pf2_1 = insertHelper9 (S n) (head (fst sorted_xs)) (tail (fst sorted_xs)) pf1_5
            -- IsSorted (S n) (tail (fst sorted_xs))

            pf2_2 = PermC_prp_2 (S n) (tail (fst sorted_xs))
            -- applyPerm (S n) Nat (Idt (S n)) (tail (fst sorted_xs)) = tail (fst sorted_xs)

            -- (k : Fin (S n)) ->
            --     LTE (index (Data.Fin.Fin (S n) implementation of Prelude.Enum, method pred k) (tail (fst sorted_xs)))
            --         (index k (tail (fst sorted_xs)))

            sorted_a_xs = insertProof (S n) a (tail (fst sorted_xs))
                ((tail (fst sorted_xs)) ** ((Idt (S n)) ** (pf2_2, pf2_1)))

            perm_a_xs = (fst (snd (sorted_a_xs)))

            perm = CPerm (S (S (S n)))
                (CPerm (S (S (S n))) (includePerm (S (S n)) (fst (snd (sorted_a_xs)))) (Swap (S (S (S n))) FZ) )
                (includePerm (S (S n)) (fst (snd (sorted_xs))))

            pf2_3 = PermC_prp_1 (S (S n)) a xs (fst (snd sorted_xs))
            -- a :: applyPerm (S (S n)) Nat (fst (snd sorted_xs)) xs =
            --     applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs)

            pf2_4 = congruence (Vect (S (S (S n))) Nat) Nat
                    (a :: (applyPerm (S (S n)) Nat (fst (snd sorted_xs)) xs))
                    (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs))
                     (\k => (index FZ k)) pf2_3
            -- a = index FZ (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs))

            pf2_5 = PermC_prp_1 (S (S n))

                       (index (FS FZ) (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs)))

                       ((index FZ (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs))) ::
                        (tail (tail (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs)))))

                        (fst (snd (insertProof (S n) a
                                                      (tail (fst sorted_xs))
                                                      (tail (fst sorted_xs) **
                                                      (Idt (S n)) **
                                                      ( (PermC_prp_2 (S n) (tail (fst sorted_xs))),
                                                        (insertHelper9 (S n) (head (fst sorted_xs)) (tail (fst sorted_xs)) pf1_5))))))

            -- now want to prove that x = (index (FS FZ) (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs)))

            pf2_6 = congruence (Vect (S (S (S n))) Nat) Nat

                        (a :: applyPerm (S (S n)) Nat (fst (snd sorted_xs)) xs)

                        (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs))

                        (\us => (index (FS FZ) us))

                        pf2_3

            -- index FZ (applyPerm (S (S n)) Nat (fst (snd sorted_xs)) xs) =
            --     index (FS FZ) (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs))

            pf2_7 = congruence (Vect (S (S n)) Nat) Nat

                    (applyPerm (S (S n)) Nat (fst (snd sorted_xs)) xs)

                    (fst (sorted_xs))

                    (\us => ((index FZ) us))

                    pf_perm_xs

             -- index FZ (applyPerm (S (S n)) Nat (fst (snd sorted_xs)) xs) = index FZ (fst sorted_xs)

            pf2_8 = trans (sym pf2_6) pf2_7

            -- index (FS FZ) (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs)) =
            --    index FZ (fst sorted_xs)

            pf2_10 = insertHelper12 (S n) (fst sorted_xs)

            -- ((index FZ (fst (sorted_xs))) = (head (fst sorted_xs)))

            pf2_11 = trans pf2_8 pf2_10

            -- index (FS FZ) (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs)) =
            -- head (fst sorted_xs)

            pf2_9 = congruence Nat (Vect (S (S (S n))) Nat)

                    (index (FS FZ) (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs)))

                    (head (fst sorted_xs)) --(index FZ (fst sorted_xs))

                    (\z => (z :: (fst (insertProof (S n)
                          a
                         (tail (fst sorted_xs))
                         (tail (fst sorted_xs) **
                          Idt (S n) **
                          (PermC_prp_2 (S n) (tail (fst sorted_xs)), insertHelper9 (S n) (head (fst sorted_xs)) (tail (fst sorted_xs)) pf1_5))))))

                    pf2_11

            -- ||||||||||||   code is running but taking too long

            {-

            pf_sorted_a_xs_total = (snd (snd sorted_a_xs))

            pf_perm_a_xs = (fst pf_sorted_a_xs_total)

            pf2_12 = congruence Nat (Vect (S (S n)) Nat) a


                (index FZ (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs)))


                (\s => (s :: (tail (fst sorted_xs))))

                pf2_4

            -- a :: tail (fst sorted_xs) =
            -- index FZ (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs)) :: tail (fst sorted_xs)

            -- want to prove
            -- (index FZ (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs)) ::
            --     tail (tail (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs)))) =
            -- (a :: tail (fst sorted_xs))

            -- check pf2_4

            -- want to prove
            -- (tail (fst sorted_xs)) = (tail (tail (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs))))


            pf2_13 = PermC_prp_1 (S (S n)) a xs (fst (snd sorted_xs))

            --  a :: applyPerm (S (S n)) Nat (fst (snd sorted_xs)) xs =
            -- applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs)

            pf2_14 = insertHelper13 (S (S n)) a (applyPerm (S (S n)) Nat (fst (snd sorted_xs)) xs)

            pf2_15 = congruence (Vect (S (S (S n))) Nat) (Vect (S (S n)) Nat)
                (a :: (applyPerm (S (S n)) Nat (fst (snd sorted_xs)) xs))
                (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs))
                (\v => (tail v))
                pf2_13

            -- applyPerm (S (S n)) Nat (fst (snd sorted_xs)) xs =
            -- tail (applyPerm (S (S (S n))) Nat (includePerm (S (S n)) (fst (snd sorted_xs))) (a :: xs))

            pf2_16 = trans (sym pf_perm_xs) pf2_15
            -}


            in
            (((head (fst sorted_xs)) :: (fst sorted_a_xs)) ** (perm ** ((trans (trans (sym pf2_5) ?rhs21) pf2_9), ?rhs22)))
