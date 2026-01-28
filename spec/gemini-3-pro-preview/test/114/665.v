Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solve (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_case: solve [-10; 20; -30; 40; -50; 60; 5; 80; -90; 100; 80; 80] = -90.
Proof. reflexivity. Qed.