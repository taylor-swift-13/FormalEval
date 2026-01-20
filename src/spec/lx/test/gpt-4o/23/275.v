Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "TTh!s40lsh!s 1s 4 str1nb0lse !n 1t
" 35.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.