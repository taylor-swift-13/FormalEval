Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_str1ng :
  Spec "str1ng" 6.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.