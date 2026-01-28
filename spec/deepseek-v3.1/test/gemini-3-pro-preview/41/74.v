Require Import Coq.Arith.Arith.

(* Specification definition *)
Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

(* Test case: input n = 92, output collisions = 8464 *)
Example car_race_collision_test : car_race_collision_spec 92 8464.
Proof.
  unfold car_race_collision_spec.
  simpl.
  reflexivity.
Qed.