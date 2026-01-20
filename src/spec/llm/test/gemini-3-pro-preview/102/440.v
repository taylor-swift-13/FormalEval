Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition choose_num (x y : Z) : Z :=
  if x >? y then -1
  else if y mod 2 =? 0 then y
  else if x =? y then -1
  else y - 1.

Example test_case_1 : choose_num 18 62 = 62.
Proof. reflexivity. Qed.