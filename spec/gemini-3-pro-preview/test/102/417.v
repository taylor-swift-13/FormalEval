Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if y <? x then -1
  else if Z.even y then y
  else if x <=? y - 1 then y - 1
  else -1.

Example test_choose_num: choose_num 28%Z 1001%Z = 1000%Z.
Proof. reflexivity. Qed.