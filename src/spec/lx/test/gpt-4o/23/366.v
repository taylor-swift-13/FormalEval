Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_vemThfGqorZJum5ymb0lsmtopsr :
  Spec "vemThfGqorZJum5ymb0lsmtopsr" 27.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.