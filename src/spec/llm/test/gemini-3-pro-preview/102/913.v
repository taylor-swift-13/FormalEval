Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if y <? x then -1
  else if Z.even y then y
  else if (y - 1) <? x then -1
  else y - 1.

Example test_case : choose_num 100 43 = -1.
Proof.
  reflexivity.
Qed.