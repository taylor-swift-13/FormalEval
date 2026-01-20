Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "ThhT    1t 1 The    i" 21.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.