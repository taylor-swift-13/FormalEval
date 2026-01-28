Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if y <? x then -1
  else
    let cand := if Z.even y then y else y - 1 in
    if cand <? x then -1 else cand.

Example test_choose_num: choose_num 17 2001 = 2000.
Proof. reflexivity. Qed.