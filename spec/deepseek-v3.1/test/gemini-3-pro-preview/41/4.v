Require Import Coq.Arith.Arith.

(* Specification definition *)
Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

(* Test case: input n = 8, output collisions = 64 *)
Example car_race_collision_test : car_race_collision_spec 8 64.
Proof.
  unfold car_race_collision_spec.
  simpl.
  reflexivity.
Qed.