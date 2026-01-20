Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_whitespace_string :
  Spec "   

  striing" 14.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.