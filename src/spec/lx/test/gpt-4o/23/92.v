Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "MThe quick brown fox jumps over the lazy This striThis is aaracter dogM" 71.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.