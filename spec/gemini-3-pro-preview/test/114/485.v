Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition min_element (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_min_element: min_element [-1; -8; 2; 4; 4; -5; 6; -7; 8; 8; -9; 0; 10] = -9.
Proof. reflexivity. Qed.