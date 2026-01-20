Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_t1t :
  Spec "t1t" 3.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.