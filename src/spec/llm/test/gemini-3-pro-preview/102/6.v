Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else
    let max_even := if Z.odd y then y - 1 else y in
    if max_even <? x then -1 else max_even.

Example test_choose_num: choose_num 27 10 = -1.
Proof. reflexivity. Qed.