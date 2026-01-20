Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : nat :=
  length (filter (Z.eqb x) l).

Definition solve (l : list Z) : Z :=
  let unique := filter (fun x => Nat.eqb (count l x) 1) l in
  match unique with
  | [] => 0
  | x :: xs => fold_left Z.min xs x
  end.

Example test_case:
  solve [20; -50; 60; -70; 80; -90; 100; 20] = -90.
Proof.
  reflexivity.
Qed.