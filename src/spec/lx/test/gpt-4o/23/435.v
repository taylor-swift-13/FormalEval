Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_single_char :
  Spec "p" 1.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.