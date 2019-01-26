module Group

%access public export

||| Given a type and a binary operation the type of proofs that the operation is associative
total
Associative : (typ : Type) -> (op : typ -> typ -> typ) -> Type 
Associative typ op = (a : typ) -> (b : typ) -> (c : typ) -> ((op (op a b) c) = (op a (op b c)))

||| Given a type and a binary operation the type of proofs that the operation is commutative
total
Commutative : (typ : Type) -> (op : typ -> typ -> typ) -> Type
Commutative typ op = (a : typ) -> (b : typ) -> ((op a b) = (op b a))

||| Given a type and a binary operation the type of proofs that identity exists
total
IdentityExists : (typ : Type) -> (op : typ -> typ -> typ) -> Type
IdentityExists typ op = ( e : typ ** (a : typ ** (( (op a e) = a), (op e a) = a))) 

||| Given a type and a binary operation the type of proofs that each element has its inverse
total
InverseExists : (typ : Type) -> (op : typ -> typ -> typ) -> Type
InverseExists typ op = (pfIden : (IdentityExists typ op) ** ((a : typ) -> (a_inv : typ ** 
                       (((op a a_inv) = (fst pfIden)), 
                       ((op a_inv a) = (fst pfIden))))))   

||| Given a type and a binary operation the type of proofs that the type along with the
||| operation is a group
total
IsGroup : (grp : Type) -> (op : grp -> grp -> grp) -> Type
IsGroup grp op = (Associative grp op, (IdentityExists grp op, InverseExists grp op))
