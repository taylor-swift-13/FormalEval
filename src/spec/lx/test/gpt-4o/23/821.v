Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "This is ao sample starintog ton test the n" 42.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.