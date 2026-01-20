Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_element (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_min_element: min_element [10; -20; 30; -40; 3; 50; -60; 70; -80; 90; -100; 10] = -100.
Proof. reflexivity. Qed.