Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_case_1: solution [10; 9; 7; 6; 5; 4; 3; 1; 1] = 1.
Proof.
  reflexivity.
Qed.