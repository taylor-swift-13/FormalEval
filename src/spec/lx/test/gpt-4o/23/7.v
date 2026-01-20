Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "This is a long string that has many characters in it" 52.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.