Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_nonempty :
  Spec "ThT    1sampLazylet 1 The    i" 30.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.