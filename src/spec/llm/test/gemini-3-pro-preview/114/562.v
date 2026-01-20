Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_element (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_min_element: min_element [1; -2; 3; -4; 6; 5; -6; 2; 7; -8; 9; 1; 4; 1; 2; 70; -1] = -8.
Proof. reflexivity. Qed.