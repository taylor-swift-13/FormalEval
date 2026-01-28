Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minimum (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_case_1: minimum [10%Z; -20%Z; -40%Z; 50%Z; -60%Z; 70%Z; -80%Z; 60%Z; 90%Z; -100%Z] = -100%Z.
Proof. reflexivity. Qed.