Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_nonempty :
  Spec "ThT    1t 1 The    i" 20.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.