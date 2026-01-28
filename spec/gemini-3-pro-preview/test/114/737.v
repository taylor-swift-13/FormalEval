Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => fold_right Z.min x xs
  end.

Example test_case : solution [-8; -9; 20; -30; 40; -50; -9; 60; -70; 80; -90; 100] = -90.
Proof.
  reflexivity.
Qed.