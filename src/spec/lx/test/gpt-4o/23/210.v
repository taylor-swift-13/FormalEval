Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "This is a sample string    This is a sampl            eto string to test the func Theon           to test the function" 118.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.