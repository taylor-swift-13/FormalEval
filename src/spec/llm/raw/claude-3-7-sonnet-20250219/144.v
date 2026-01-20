
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition simplify_spec (x n : string) (res : bool) : Prop :=
  exists x1 x2 n1 n2 : Z,
    (x1 > 0 /\ x2 > 0 /\ n1 > 0 /\ n2 > 0) /\
    (x = (Z.to_string x1) ++ "/" ++ (Z.to_string x2)) /\
    (n = (Z.to_string n1) ++ "/" ++ (Z.to_string n2)) /\
    (res = Z.eqb ((x1 * n1) mod (x2 * n2)) 0).
