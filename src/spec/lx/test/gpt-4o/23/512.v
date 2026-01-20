Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_vemThfGqorZJum5ymb0lsmtstgrsr1ngLqNCZAtestpsr :
  Spec "vemThfGqorZJum5ymb0lsmtstgrsr1ngLqNCZAtestpsr" 45.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.