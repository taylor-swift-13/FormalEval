Require Import ZArith.
Require Import Lia.

Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = n * n.

Example car_race_collision_test : car_race_collision_spec 2 4.
Proof.
  unfold car_race_collision_spec.
  simpl.
  reflexivity.
Qed.