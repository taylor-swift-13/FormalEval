Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_space :
  Spec " " 1.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.