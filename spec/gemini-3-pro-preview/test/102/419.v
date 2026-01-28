Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if y <? x then -1
  else if Z.even y then y
  else if y - 1 <? x then -1
  else y - 1.

Example check : choose_num 24 26 = 26.
Proof.
  reflexivity.
Qed.