Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition min_element (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_min_element: min_element [10%Z; -20%Z; 30%Z; -40%Z; 3%Z; 50%Z; 21%Z; 70%Z; -80%Z; 89%Z; -100%Z; 10%Z] = (-100)%Z.
Proof. reflexivity. Qed.