Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_case: solution [-1; 2; -3; 4; 6; -7; 8; -9; 10] = -9.
Proof.
  reflexivity.
Qed.