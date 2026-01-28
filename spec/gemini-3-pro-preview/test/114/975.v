Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition min_element (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_min_element: min_element [-30%Z; -9%Z; 20%Z; -30%Z; 40%Z; -50%Z; 80%Z; 80%Z; -90%Z; 100%Z; 20%Z] = -90%Z.
Proof. reflexivity. Qed.