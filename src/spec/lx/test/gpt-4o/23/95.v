Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "1234 This sitriThis is a long string that has many characters in itng has a 
 neThe quick brown f ox jumps over the lazygwline character5" 137.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.