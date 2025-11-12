Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition starts_one_ends_spec (n count : Z) : Prop :=
  n >= 1 /\
  ((n = 1 /\ count = 1) \/
   (n > 1 /\ count = 18 * Z.pow 10 (Z.to_nat (n - 2)))).