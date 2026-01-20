Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_special_chars :
  Spec "   

wwtes            ls    Th!s 1s 4 str1ng wtest5ymb0ls !n 1t
 " 65.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.