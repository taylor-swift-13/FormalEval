Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_case: solution [3; 2; -5; 4; 0; 1; -3; 2; -2; 5] = -5.
Proof.
  reflexivity.
Qed.