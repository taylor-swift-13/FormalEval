Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if Z.even y then y
  else if x =? y then -1
  else y - 1.

Example test_choose_num: choose_num 19%Z 32%Z = 32%Z.
Proof. reflexivity. Qed.