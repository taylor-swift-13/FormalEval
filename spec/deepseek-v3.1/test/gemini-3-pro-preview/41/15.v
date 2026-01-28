Require Import Coq.Arith.Arith.

(* Specification definition *)
Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

(* Test case: input n = 500, output collisions = 250000 *)
Example car_race_collision_test : car_race_collision_spec 500 250000.
Proof.
  unfold car_race_collision_spec.
  simpl.
  reflexivity.
Qed.