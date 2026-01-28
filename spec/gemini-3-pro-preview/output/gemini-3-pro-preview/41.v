Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition car_race_collision_spec (n : Z) (result : Z) : Prop :=
  result = n * n.

Example test_car_race_collision : car_race_collision_spec 2 4.
Proof.
  unfold car_race_collision_spec.
  reflexivity.
Qed.