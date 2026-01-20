Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if (y mod 2) =? 0 then y
  else if x =? y then -1
  else y - 1.

Example check: choose_num 24 30 = 30.
Proof.
  reflexivity.
Qed.