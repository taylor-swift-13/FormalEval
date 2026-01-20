Require Import Arith.
Require Import ZArith.
Open Scope Z_scope.

Definition Spec(input output : Z) : Prop :=
  output = input * input.

Example test_car_race_collision :
  Spec 2 4.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.