Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition min_element (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_min_element_1 : min_element [100000; 1; -1; 1; -1; 1; -1; 1; 2; 1; -1; 1; -1; 1; -1; 90; 0; 1; -1; 1; -1; 1; -1; 1; -1; 2; -1; 1; -1; 1; -1; 1] = -1.
Proof. reflexivity. Qed.