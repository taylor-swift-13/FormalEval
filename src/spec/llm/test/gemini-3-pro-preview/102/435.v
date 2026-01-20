Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if Z.even y then y
  else if x >? y - 1 then -1
  else y - 1.

Example test_choose_num: choose_num 12%Z 29%Z = 28%Z.
Proof. reflexivity. Qed.