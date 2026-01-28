Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if y <? x then -1
  else if (y mod 2) =? 0 then y
  else if x =? y then -1
  else y - 1.

Example test_choose_num: choose_num 29 997 = 996.
Proof.
  reflexivity.
Qed.