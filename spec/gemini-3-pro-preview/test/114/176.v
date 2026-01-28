Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_case: solution [10; -20; 30; -40; 50; 1; 70; -80; 60; 90; -100] = -100.
Proof.
  reflexivity.
Qed.