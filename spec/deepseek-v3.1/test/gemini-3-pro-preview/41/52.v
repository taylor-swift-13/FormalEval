Require Import Coq.Arith.Arith.

(* Specification definition *)
Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

(* Test case: input n = 31, output collisions = 961 *)
Example car_race_collision_test : car_race_collision_spec 31 961.
Proof.
  unfold car_race_collision_spec.
  simpl.
  reflexivity.
Qed.