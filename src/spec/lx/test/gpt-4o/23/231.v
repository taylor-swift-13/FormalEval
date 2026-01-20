Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "The QuiisJumpsck Brown Fox Jg" 29.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.