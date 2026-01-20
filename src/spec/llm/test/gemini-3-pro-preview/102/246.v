Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else
    let val := if Z.even y then y else y - 1 in
    if val <? x then -1 else val.

Example test_choose_num: choose_num 33 24 = -1.
Proof. reflexivity. Qed.