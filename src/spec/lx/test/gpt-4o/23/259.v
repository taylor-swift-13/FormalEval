Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "This is a sample string    This is a sampl            eto string to LqNCZAtest the func Theon           to test the function" 124.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.