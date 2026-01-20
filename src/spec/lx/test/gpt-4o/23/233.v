Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_Jum5ymb0lsmfunction :
  Spec "Jum5ymb0lsmfunction" 19.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.