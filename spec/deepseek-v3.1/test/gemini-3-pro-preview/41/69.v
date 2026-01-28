Require Import Coq.Arith.Arith.

(* Specification definition *)
Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

(* Test case: input n = 997, output collisions = 994009 *)
Example car_race_collision_test : car_race_collision_spec 997 994009.
Proof.
  unfold car_race_collision_spec.
  vm_compute.
  reflexivity.
Qed.