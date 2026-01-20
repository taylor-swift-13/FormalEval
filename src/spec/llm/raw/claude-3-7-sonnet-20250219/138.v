
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition is_equal_to_sum_even_spec (n : Z) (res : bool) : Prop :=
  res = (Z.leb 8 n && Z.even n).
