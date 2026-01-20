Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "The quick brown fox11234567890 jumps over the lazy This striThis is aaracter dog" 80.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.