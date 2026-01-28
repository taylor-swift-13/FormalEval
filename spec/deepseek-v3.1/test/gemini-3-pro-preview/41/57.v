Require Import Coq.Arith.Arith.

(* Specification definition *)
Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

(* Test case: input n = 1003, output collisions = 1006009 *)
Example car_race_collision_test : car_race_collision_spec 1003 1006009.
Proof.
  unfold car_race_collision_spec.
  vm_compute.
  reflexivity.
Qed.