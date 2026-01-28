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

Example test_smallest_change : smallest_change_spec [(-10); (-8); (-8); (-7); 2; (-5); (-4); (-3); (-2); (-1); (-9); 1; 2; 3; 3; 5; 6; 7; 9; 10; (-3); 6; 1; (-7); 3] 12%nat.
Proof.
  unfold smallest_change_spec.
  reflexivity.
Qed.