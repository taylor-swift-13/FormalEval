Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "    1t 1  The    " 17.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.