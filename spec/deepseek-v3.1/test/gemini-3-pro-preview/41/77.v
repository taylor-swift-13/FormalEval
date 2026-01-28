Require Import Coq.Arith.Arith.

(* Specification definition *)
Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

(* Test case: input n = 54, output collisions = 2916 *)
Example car_race_collision_test : car_race_collision_spec 54 2916.
Proof.
  unfold car_race_collision_spec.
  simpl.
  reflexivity.
Qed.