Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else
    let res := if Z.even y then y else y - 1 in
    if res <? x then -1 else res.

Example test_choose_num: choose_num 22 31 = 30.
Proof. reflexivity. Qed.