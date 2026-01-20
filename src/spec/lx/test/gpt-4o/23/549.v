Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_spaces_and_chars :
  Spec "   

RL 1Ls  " 13.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.