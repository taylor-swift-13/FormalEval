Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "The quick brown fox jumps over the lazy Thisthree
four
fiveracter dog" 69.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.