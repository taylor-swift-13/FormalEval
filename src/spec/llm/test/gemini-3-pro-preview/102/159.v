From Coq Require Import String List ZArith.
From Coq Require Import Init.Datatypes.
Open Scope string_scope.
Open Scope Z_scope.
Import ListNotations.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if Z.even y then y
  else if x =? y then -1
  else y - 1.

Example check : choose_num 10%Z 10%Z = 10%Z.
Proof. reflexivity. Qed.