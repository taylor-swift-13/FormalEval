Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if Z.even y then y
  else if x >? y - 1 then -1
  else y - 1.

Example test_case_1 : choose_num 24 29 = 28.
Proof. reflexivity. Qed.