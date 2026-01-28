Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else
    let max_even := if Z.even y then y else y - 1 in
    if max_even <? x then -1 else max_even.

Example test_choose_num: choose_num 102 15 = -1.
Proof. reflexivity. Qed.