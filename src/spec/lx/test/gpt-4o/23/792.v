Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_tVtV :
  Spec "tVtV" 4.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.