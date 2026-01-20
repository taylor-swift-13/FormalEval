Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "Fo stgrsr1ng   This is aTh!s 1s 4 str1ng wtest5ymb0lse !n 1t
 sampleto string to test the function  n        x" 110.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.