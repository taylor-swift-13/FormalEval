Require Import List.
Require Import Arith.

Import ListNotations.

Definition generate_integers_spec (a b : nat) (evens : list nat) : Prop :=
  let (a, b) := if a <=? b then (a, b) else (b, a) in
  evens = filter (fun i => i mod 2 =? 0) (seq a (min (b + 1) 10 - a)).

Example generate_integers_spec_2_10 :
  generate_integers_spec 2 10 [2; 4; 6; 8].
Proof.
  unfold generate_integers_spec.
  simpl.
  reflexivity.
Qed.