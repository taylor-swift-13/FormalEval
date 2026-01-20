Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_why1NcJH1th :
  Spec "why1NcJH1th" 11.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.