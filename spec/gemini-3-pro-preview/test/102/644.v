Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if Z.even y then y
  else if y =? x then -1
  else y - 1.

Example test_choose_num: choose_num 23 2001 = 2000.
Proof. reflexivity. Qed.