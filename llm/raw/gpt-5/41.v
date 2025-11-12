Require Import Coq.ZArith.ZArith.

Definition car_race_collision_spec (n : Z) (collisions : Z) : Prop :=
  collisions = n * n.