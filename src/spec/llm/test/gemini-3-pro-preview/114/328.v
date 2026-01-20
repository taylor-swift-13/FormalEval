Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition min_element (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Example test_min_element: min_element [1%Z; -2%Z; 3%Z; -4%Z; 5%Z; -6%Z; 7%Z; -8%Z; 9%Z; 4%Z; -3%Z; 2%Z; -1%Z; -1%Z] = -8%Z.
Proof. reflexivity. Qed.