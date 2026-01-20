Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if y <? x then -1
  else let candidate := if Z.even y then y else y - 1 in
       if candidate <? x then -1 else candidate.

Example test_choose_num : choose_num 18 21 = 20.
Proof. reflexivity. Qed.