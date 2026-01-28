Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition car_race_collision_spec (n : Z) (collisions : Z) : Prop :=
  collisions = n * n.

Example test_car_race_collision : car_race_collision_spec 9998 99960004.
Proof.
  unfold car_race_collision_spec.
  reflexivity.
Qed.