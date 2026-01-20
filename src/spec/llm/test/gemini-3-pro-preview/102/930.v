Require Import Coq.ZArith.ZArith.
Local Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if Z.even y then y
  else if x =? y then -1
  else y - 1.

Example example_new: choose_num 16 2002 = 2002.
Proof. reflexivity. Qed.