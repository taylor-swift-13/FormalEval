Require Import Coq.Arith.Arith.

Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

Example car_race_collision_test : car_race_collision_spec 1002 1004004.
Proof.
  unfold car_race_collision_spec.
  vm_compute.
  reflexivity.
Qed.