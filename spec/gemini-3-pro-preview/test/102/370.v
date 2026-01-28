Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if y mod 2 =? 0 then y
  else if y - 1 >=? x then y - 1
  else -1.

Example test_choose_num: choose_num 34 4 = -1.
Proof. reflexivity. Qed.