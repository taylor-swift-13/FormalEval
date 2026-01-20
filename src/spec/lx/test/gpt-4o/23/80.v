Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "The quick brown f ox jumps over the lazy" 40.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.