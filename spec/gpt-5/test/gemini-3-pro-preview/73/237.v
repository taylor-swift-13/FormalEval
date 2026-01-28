Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Import ListNotations.

Definition smallest_change_spec (arr : list Z) (res : nat) : Prop :=
  let half := Nat.div (length arr) 2 in
  let first := firstn half arr in
  let rfirst := firstn half (rev arr) in
  res = length (filter (fun p => negb (Z.eqb (fst p) (snd p))) (combine first rfirst)).

Open Scope Z_scope.

Example test_smallest_change : smallest_change_spec [-10; -9; -8; -7; -6; -5; -4; -3; -2; -8; -1; 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; -8] 11%nat.
Proof.
  unfold smallest_change_spec.
  reflexivity.
Qed.