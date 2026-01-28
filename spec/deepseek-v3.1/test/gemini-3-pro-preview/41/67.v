Require Import Coq.Arith.Arith.

(* Specification definition *)
Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

(* Test case: input n = 998, output collisions = 996004 *)
Example car_race_collision_test : car_race_collision_spec 998 996004.
Proof.
  unfold car_race_collision_spec.
  reflexivity.
Qed.