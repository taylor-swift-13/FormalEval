Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "     str1ng 1t  The    This is a samp leOvering to test the function" 68.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.