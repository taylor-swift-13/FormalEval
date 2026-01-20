Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_alphabet :
  Spec "abcdefghijklmnopqrstuvwxyz" 26.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.