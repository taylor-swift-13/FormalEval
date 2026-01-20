Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else 
    let target := if Z.even y then y else y - 1 in
    if target <? x then -1 else target.

Example test_choose_num: choose_num 2 5 = 4.
Proof.
  reflexivity.
Qed.