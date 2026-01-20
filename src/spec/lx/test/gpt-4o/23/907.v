Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_non_empty :
  Spec "Th!s 1s 4 str1str1 1t" 21.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.