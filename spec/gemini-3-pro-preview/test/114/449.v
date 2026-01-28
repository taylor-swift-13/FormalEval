Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition minimum (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_minimum: minimum [100000%Z; -2%Z; 3%Z; 7%Z; 5%Z; -6%Z; 8%Z; 90%Z; -8%Z; 9%Z; 4%Z; -3%Z; 2%Z; -1%Z; 9%Z] = -8%Z.
Proof.
  simpl. reflexivity.
Qed.