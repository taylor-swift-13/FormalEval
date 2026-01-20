Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if y <? x then -1
  else if (y mod 2) =? 0 then y
  else if x =? y then -1
  else y - 1.

Example choose_num_example : choose_num 997 2001 = 2000.
Proof.
  compute.
  reflexivity.
Qed.