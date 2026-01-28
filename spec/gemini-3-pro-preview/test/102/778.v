Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if y <? x then -1
  else if Z.even y then y
  else if x <=? y - 1 then y - 1
  else -1.

Example check: choose_num 44 6 = -1.
Proof.
  simpl.
  reflexivity.
Qed.