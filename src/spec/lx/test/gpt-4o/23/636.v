Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "This is a sample strintog ton test the function" 47.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.