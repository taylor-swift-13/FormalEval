Require Import Arith.

Definition Spec(input output : nat) : Prop :=
  output = input * input.


Example test_car_race_collision :
  Spec 2 4.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.