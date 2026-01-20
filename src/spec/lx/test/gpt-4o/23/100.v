Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "The quick brown fox jumps over theThe quick brown fox jxumps overq the lazy dog lazy Thisthree
four
fiveracter dog" 114.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.