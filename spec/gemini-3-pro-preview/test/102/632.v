Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  let target := if Z.even y then y else y - 1 in
  if target <? x then -1 else target.

Example test_choose_num: choose_num 31 21 = -1.
Proof.
  reflexivity.
Qed.