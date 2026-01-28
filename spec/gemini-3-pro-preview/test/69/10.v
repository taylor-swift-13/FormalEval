Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_case_1: solve [6; 9; 6; 7; 1; 4; 7; 1; 8; 8; 9; 8; 10; 10; 8; 4; 10; 4; 10; 1; 2; 9; 5; 7; 9] = 1.
Proof.
  reflexivity.
Qed.