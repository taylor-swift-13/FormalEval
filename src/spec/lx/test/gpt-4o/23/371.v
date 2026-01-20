Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_FoF1Thisxuk :
  Spec "FoF1Thisxuk" 11.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.