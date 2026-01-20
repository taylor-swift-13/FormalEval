Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  let n := if Z.even y then y else y - 1 in
  if n <? x then -1 else n.

Example test_choose_num : choose_num 10 28 = 28.
Proof. reflexivity. Qed.