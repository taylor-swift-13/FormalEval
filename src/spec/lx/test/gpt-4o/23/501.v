Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_t1 :
  Spec "t1" 2.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.