Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_function :
  Spec "    

 func!ntion  " 19.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.