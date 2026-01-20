Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_spaces_and_text :
  Spec "    1t  Theion    " 18.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.