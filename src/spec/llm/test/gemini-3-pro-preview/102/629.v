Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if Z.even y then y
  else if x =? y then -1
  else y - 1.

Example choose_num_example : choose_num 9 2000 = 2000.
Proof. reflexivity. Qed.