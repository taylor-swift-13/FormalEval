Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition min_element (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Example test_min_element: min_element [-1; 2; -3; 4; -5; 6; -7; 10; -7] = -7.
Proof. reflexivity. Qed.