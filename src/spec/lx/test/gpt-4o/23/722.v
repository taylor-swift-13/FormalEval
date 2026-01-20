Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_whitespace_and_characters :
  Spec "    1t 1   " 11.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.