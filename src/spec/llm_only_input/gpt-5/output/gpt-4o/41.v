Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Definition car_race_collision_spec (n : nat) (collisions : nat) : Prop :=
  collisions = (n * n)%nat.

Example car_race_collision_spec_test_case :
  let input := [2%Z] in
  let output := 4%Z in
  car_race_collision_spec (Z.to_nat (hd 0%Z input)) (Z.to_nat output).
Proof.
  cbn.
  unfold car_race_collision_spec.
  cbn.
  reflexivity.
Qed.