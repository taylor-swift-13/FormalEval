Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition min_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_min_list:
  min_list [1; -1; 1; -1; 1; -1; 1; 1; -1; 1; -1; 1; -1; 90; 0; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; -1; 1; 0; 1; -1] = -1.
Proof.
  reflexivity.
Qed.