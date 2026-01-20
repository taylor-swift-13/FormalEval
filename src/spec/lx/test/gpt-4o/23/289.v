Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "    This irs a sample string to tea  " 37.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.