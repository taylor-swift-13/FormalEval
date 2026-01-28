Require Import Coq.Arith.Arith.

(* Specification definition *)
Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

Example car_race_collision_test : car_race_collision_spec 999 998001.
Proof.
  unfold car_race_collision_spec.
  reflexivity.
Qed.