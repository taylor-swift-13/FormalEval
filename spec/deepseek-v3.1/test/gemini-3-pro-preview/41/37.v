Require Import Coq.Arith.Arith.

(* Specification definition *)
Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

(* Test case: input n = 501, output collisions = 251001 *)
Example car_race_collision_test : car_race_collision_spec 501 251001.
Proof.
  unfold car_race_collision_spec.
  simpl.
  reflexivity.
Qed.