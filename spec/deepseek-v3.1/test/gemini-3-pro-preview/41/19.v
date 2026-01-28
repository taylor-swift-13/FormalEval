Require Import Coq.Arith.Arith.

(* Specification definition *)
Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

(* Test case: input n = 99, output collisions = 9801 *)
Example car_race_collision_test : car_race_collision_spec 99 9801.
Proof.
  unfold car_race_collision_spec.
  simpl.
  reflexivity.
Qed.