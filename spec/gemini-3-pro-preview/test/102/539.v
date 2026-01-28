Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if y mod 2 =? 0 then y
  else if x =? y then -1
  else y - 1.

Example test_case_1: choose_num 996%Z 2001%Z = 2000%Z.
Proof. reflexivity. Qed.