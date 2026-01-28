Require Import Coq.Arith.Arith.

(* Specification definition *)
Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

(* Test case: input n = 58, output collisions = 3364 *)
Example car_race_collision_test : car_race_collision_spec 58 3364.
Proof.
  unfold car_race_collision_spec.
  simpl.
  reflexivity.
Qed.