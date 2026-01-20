Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "striing     This is a sampl          tothe func tion          " 62.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.