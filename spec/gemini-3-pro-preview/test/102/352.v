Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if Z.even y then y
  else if y - 1 >=? x then y - 1
  else -1.

Example test_choose_num: choose_num 25 100 = 100.
Proof. reflexivity. Qed.