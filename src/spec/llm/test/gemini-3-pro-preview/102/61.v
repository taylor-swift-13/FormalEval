From Coq Require Import String ZArith.
Local Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if Z.even y then y
  else if x =? y then -1
  else y - 1.

Example test_choose_num : choose_num 100 15 = -1.
Proof. reflexivity. Qed.