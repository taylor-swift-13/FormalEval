Require Import Arith.

Definition Spec(input output : nat) : Prop :=
  output = input * input.

Example collision_test :
  Spec 20 400.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.