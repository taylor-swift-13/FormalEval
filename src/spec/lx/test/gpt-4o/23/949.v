Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "MNhqThe CQugicJumpsk Brown Foxstr1str1ngng Jumps OverThis is a sample string to test thCV" 89.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.