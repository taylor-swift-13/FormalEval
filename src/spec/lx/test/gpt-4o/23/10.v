Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sentence :
  Spec "The quick brown fox jumps over the lazy dog" 43.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.