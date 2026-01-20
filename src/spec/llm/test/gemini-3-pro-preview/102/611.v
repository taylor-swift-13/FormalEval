Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else
    let ans := if Z.even y then y else y - 1 in
    if ans <? x then -1 else ans.

Example test_choose_num: choose_num 7 31 = 30.
Proof. reflexivity. Qed.