Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "mThftGqorZJum5ymb0lsmtstricQukicknops" 37.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.