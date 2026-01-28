Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if Z.gtb x y then -1
  else if Z.even y then y
  else if Z.geb (y - 1) x then y - 1
  else -1.

Example test_choose_num: choose_num 22 21 = -1.
Proof. reflexivity. Qed.