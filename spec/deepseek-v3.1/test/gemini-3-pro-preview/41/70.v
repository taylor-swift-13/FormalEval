Require Import Coq.Arith.Arith.

(* Specification definition *)
Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

(* Test case: input n = 996, output collisions = 992016 *)
Example car_race_collision_test : car_race_collision_spec 996 992016.
Proof.
  unfold car_race_collision_spec.
  vm_compute.
  reflexivity.
Qed.