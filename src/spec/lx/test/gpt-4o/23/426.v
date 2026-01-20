Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_str1nb0lse :
  Spec "str1nb0lse" 10.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.