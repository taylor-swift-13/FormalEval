Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "why1N    This is a sampleto string to test e function          cJH1th" 69.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.