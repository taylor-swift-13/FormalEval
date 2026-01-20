Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "TTh!s40lsh!s 1s 4 str1ng wtest5ymb0lse !n 1t
" 45.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.