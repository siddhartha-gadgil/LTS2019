module DecDet

-- the deterministic decidable type. 

DecHelper : (prop : Type) -> Bool -> Type
DecHelper prop True = (ans : Bool ** ( pf_of_ans ans )) where
    pf_of_ans True = prop
    pf_of_ans False = prop -> Void
DecHelper prop False = Unit

--IsDecided : Type
--IsDecided = (prop : Type ** ( isdecided ** Bool  ))
