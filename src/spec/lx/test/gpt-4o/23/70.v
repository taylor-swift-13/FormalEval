Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "G1The quick brown f ox jumps over the lazy dog234  has a 
 newline character5NDKQyadEb" 86.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.