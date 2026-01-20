Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_element (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_min_element: min_element [-1%Z; -8%Z; 2%Z; 4%Z; 4%Z; -5%Z; 6%Z; -7%Z; 8%Z; -9%Z; 0%Z; 10%Z] = -9%Z.
Proof. reflexivity. Qed.