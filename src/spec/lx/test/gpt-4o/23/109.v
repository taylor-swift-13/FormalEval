Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "The Quick Brown Fox Jumps Over The Lazy Dog" 43.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.