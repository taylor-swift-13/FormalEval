Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition count (l : list Z) (x : Z) : nat :=
  length (filter (Z.eqb x) l).

Definition solution (l : list Z) : Z :=
  let unique := filter (fun x => Nat.eqb (count l x) 1) l in
  match unique with
  | [] => 0
  | h :: t => fold_left Z.min t h
  end.

Example test_case: solution [-8; 101; -8; 20; 40; -50; 60; 80; 100; -9] = -50.
Proof. reflexivity. Qed.