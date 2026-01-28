Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition find_min (l : list Z) : Z :=
  match l with
  | nil => 0
  | x :: xs => fold_right Z.min x xs
  end.

Example test_case: find_min [1%Z; -2%Z; 3%Z; -5%Z; 5%Z; -6%Z; 7%Z; 5%Z; -8%Z; 9%Z; 4%Z; 2%Z; 70%Z; -1%Z; 5%Z; -2%Z; -2%Z] = -8%Z.
Proof. reflexivity. Qed.