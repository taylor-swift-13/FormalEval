Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else
    let target := if Z.odd y then y - 1 else y in
    if target <? x then -1 else target.

Example test_case_1 : choose_num 21 3 = -1.
Proof. reflexivity. Qed.