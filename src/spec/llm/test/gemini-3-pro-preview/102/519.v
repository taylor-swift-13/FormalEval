Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if y <? x then -1
  else if Z.even y then y
  else if x <=? y - 1 then y - 1
  else -1.

Example choose_num_test : choose_num 29 99 = 98.
Proof. reflexivity. Qed.