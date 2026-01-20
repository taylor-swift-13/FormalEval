Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "te      1t  The    stt" 22.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.