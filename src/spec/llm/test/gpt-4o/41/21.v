Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Open Scope Z_scope.

Definition car_race_collision_spec (n : Z) (collisions : Z) : Prop :=
  collisions = n * n.

Example car_race_collision_test :
  car_race_collision_spec 19 361.
Proof.
  unfold car_race_collision_spec.
  simpl.
  reflexivity.
Qed.

Close Scope Z_scope.