Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_case: solve [-1; 1; -1; 1; -1; 1; -1; 0; 1; -1; 1; -1; 1; -1; 1; -1; 30; -1; 1; -1; 1; 1; -1; 1; -1; 1; -1; 1; -1; 1] = -1.
Proof.
  compute. reflexivity.
Qed.