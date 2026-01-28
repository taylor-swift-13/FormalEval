Require Import Coq.Arith.Arith.

(* Specification definition *)
Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

(* Test case: input n = 59, output collisions = 3481 *)
Example car_race_collision_test : car_race_collision_spec 59 3481.
Proof.
  unfold car_race_collision_spec.
  simpl.
  reflexivity.
Qed.