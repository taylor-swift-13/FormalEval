Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_non_empty :
  Spec "The quick brown f ox jumps over the lazyg" 41.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.