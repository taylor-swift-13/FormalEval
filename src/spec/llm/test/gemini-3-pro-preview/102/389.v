Require Import ZArith.
Local Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if y <? x then -1
  else if Z.even y then y
  else if (y - 1) <? x then -1
  else y - 1.

Example test_case: choose_num 62 62 = 62.
Proof. reflexivity. Qed.