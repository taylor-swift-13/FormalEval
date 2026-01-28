From Coq Require Import List.
From Coq Require Import ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if Z.even y then y
  else if x <=? y - 1 then y - 1
  else -1.

Example test_choose_num: choose_num 33 6 = -1.
Proof. reflexivity. Qed.