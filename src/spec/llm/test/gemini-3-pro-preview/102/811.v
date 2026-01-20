Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  let target := y - (y mod 2) in
  if target <? x then -1 else target.

Example test_choose_num: choose_num 30 15 = -1.
Proof. reflexivity. Qed.