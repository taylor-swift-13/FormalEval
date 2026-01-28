Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition minimum (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Example test_minimum: minimum [-100; 50; -50; 100; -100; 50; -50; 100; -100; 50; -50; 100; -100; 50; -50; 100; 3; 50; -50; 100] = -100.
Proof. reflexivity. Qed.