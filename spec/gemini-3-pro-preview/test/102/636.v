Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if Z.even y then y
  else if x >? y - 1 then -1
  else y - 1.

Example test_choose_num: choose_num 29%Z 23%Z = (-1)%Z.
Proof.
  reflexivity.
Qed.