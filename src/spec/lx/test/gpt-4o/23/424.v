Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_with_spaces :
  Spec "   

RL 1s  " 12.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.