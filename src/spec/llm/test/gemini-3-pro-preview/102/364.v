From Coq Require Import Strings.String.
From Coq Require Import ZArith.ZArith.
From Coq Require Import Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if Z.even y then y
  else if x <=? (y - 1) then y - 1
  else -1.

Example test_choose_num: choose_num 30 7 = -1.
Proof. reflexivity. Qed.