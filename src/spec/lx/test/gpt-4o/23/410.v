Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "    This is a sampl           eto string to test thes func tion          " 73.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.