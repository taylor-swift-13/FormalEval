Require Import Coq.Arith.Arith.

(* Specification definition *)
Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

(* Test case: input n = 101, output collisions = 10201 *)
Example car_race_collision_test : car_race_collision_spec 101 10201.
Proof.
  unfold car_race_collision_spec.
  simpl.
  reflexivity.
Qed.