Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "Testing te stingone
twot
thrThis is a long strinThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazy Thisthree
four
fiveracter dogg that has many characters in itee
four
five 123" 209.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.