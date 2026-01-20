Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_rl4 :
  Spec "RL4" 3.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.