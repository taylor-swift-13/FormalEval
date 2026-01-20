Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_string4cJH1Jth :
  Spec "string4cJH1Jth" 14.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.