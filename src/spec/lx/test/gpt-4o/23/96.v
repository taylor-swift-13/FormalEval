Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "912345667890The quick brown fox jumps over the lazy This striThis is aaracter dogM" 82.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.