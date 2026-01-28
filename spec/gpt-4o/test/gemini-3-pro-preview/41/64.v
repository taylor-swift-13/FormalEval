Require Import Coq.Arith.Arith.

Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

Example test_car_race_collision : car_race_collision_spec 58 3364.
Proof.
  unfold car_race_collision_spec.
  simpl.
  reflexivity.
Qed.