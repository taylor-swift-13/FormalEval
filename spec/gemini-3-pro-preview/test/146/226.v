Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_palindrome (l : list Z) : Z :=
  if list_eq_dec Z.eq_dec l (rev l) then 1 else 0.

Example test_case: is_palindrome [-123; 456; 789; 456; -123] = 1.
Proof.
  reflexivity.
Qed.