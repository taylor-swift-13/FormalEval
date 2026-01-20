Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if Z.even y then y
  else if y - 1 >=? x then y - 1
  else -1.

Example choose_num_example : choose_num 1002 1001 = -1.
Proof.
  reflexivity.
Qed.