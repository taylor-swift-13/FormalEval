Require Import Arith.

Definition Spec(input output : nat) : Prop :=
  output = input * input.

Example collision_test :
  Spec 101 10201.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.