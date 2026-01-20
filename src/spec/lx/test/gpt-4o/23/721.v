Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_spaces_and_special_chars :
  Spec "    

 !func!ntion  " 20.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.