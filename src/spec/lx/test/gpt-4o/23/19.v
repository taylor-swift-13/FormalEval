Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "The quick brown fox jumps over the lazy This striThis is a long string that has many characters in itng has a 
 newline character dog" 133.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.