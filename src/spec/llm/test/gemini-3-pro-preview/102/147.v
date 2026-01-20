Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if Z.even y then y
  else if y - 1 <? x then -1
  else y - 1.

Example check_choose_num : choose_num 32 1 = -1.
Proof.
  reflexivity.
Qed.