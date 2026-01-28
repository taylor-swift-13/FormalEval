Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition min_element (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_min_element:
  min_element [-8; -9; 20; -30; 40; -50; 60; 80; -70; 80; -90; 100] = -90.
Proof. reflexivity. Qed.