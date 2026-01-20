Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "thrieeThe quick brown fox jumps overq the lazy dog
four
five" 60.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.