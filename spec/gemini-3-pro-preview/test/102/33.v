Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if y <? x then -1
  else if y mod 2 =? 0 then y
  else if y - 1 <? x then -1
  else y - 1.

Example test_choose_num: choose_num 35 200 = 200.
Proof. reflexivity. Qed.