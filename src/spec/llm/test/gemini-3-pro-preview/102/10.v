From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.
Local Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if y mod 2 =? 0 then y
  else if x =? y then -1
  else y - 1.

Example test_choose_num: choose_num 30 30 = 30.
Proof. reflexivity. Qed.