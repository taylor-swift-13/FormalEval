Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition min_element (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_case: min_element [-8%Z; -9%Z; 20%Z; -30%Z; 40%Z; -50%Z; 60%Z; 80%Z; -70%Z; 80%Z; -90%Z; 100%Z; 20%Z] = -90%Z.
Proof. reflexivity. Qed.