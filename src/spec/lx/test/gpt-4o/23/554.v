Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_hyNJcJ :
  Spec "hyNJcJ" 6.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.