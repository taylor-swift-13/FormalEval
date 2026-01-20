Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_spaces :
  Spec "    1t 1 The    aaaaa" 21.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.