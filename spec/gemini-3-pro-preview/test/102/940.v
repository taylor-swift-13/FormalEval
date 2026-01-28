Require Import ZArith.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if y <? x then -1
  else if Z.even y then y
  else if x <=? y - 1 then y - 1
  else -1.

Example test_choose_num : choose_num 2 999 = 998.
Proof.
  reflexivity.
Qed.