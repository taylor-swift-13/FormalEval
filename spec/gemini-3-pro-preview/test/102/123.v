Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if y <? x then -1
  else if Z.even y then y
  else if (y - 1) <? x then -1
  else y - 1.

Example check_choose_num_20_21 : choose_num 20 21 = 20.
Proof.
  reflexivity.
Qed.