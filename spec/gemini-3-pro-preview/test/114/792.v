Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_element (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_min_element: min_element [2; -1; 0; 1; 1; -1; 1; -100; 1; -1; 1; -1] = -100.
Proof. reflexivity. Qed.