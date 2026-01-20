Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if y <? x then -1
  else if Z.even y then y
  else if y =? x then -1
  else y - 1.

Example test_choose_num : choose_num 2000 18 = -1.
Proof. reflexivity. Qed.