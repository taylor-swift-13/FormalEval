Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else
    let max_val := if Z.even y then y else y - 1 in
    if max_val <? x then -1 else max_val.

Example test_choose_num: choose_num 12 23 = 22.
Proof. reflexivity. Qed.