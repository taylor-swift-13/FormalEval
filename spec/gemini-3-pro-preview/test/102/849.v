Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else
    let n := if Z.even y then y else y - 1 in
    if n <? x then -1 else n.

Example test_choose_num: choose_num 100 5 = -1.
Proof. reflexivity. Qed.