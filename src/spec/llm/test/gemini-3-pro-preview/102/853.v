Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if y <? x then -1
  else if Z.even y then y
  else if (y - 1) <? x then -1
  else y - 1.

Example test_choose_num: choose_num 3 998 = 998.
Proof.
  reflexivity.
Qed.