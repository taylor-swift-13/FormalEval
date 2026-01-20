Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample_string :
  Spec "   This is a sample stringunction

   z" 39.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.