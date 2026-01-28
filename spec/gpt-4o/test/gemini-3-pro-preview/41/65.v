Require Import Coq.Arith.Arith.

Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

Example test_car_race_collision : car_race_collision_spec 999 998001.
Proof.
  unfold car_race_collision_spec.
  reflexivity.
Qed.