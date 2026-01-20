Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "This is ao sample starintog ton test the function" 49.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.