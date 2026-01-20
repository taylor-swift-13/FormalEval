Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_space :
  Spec "Tis          " 13.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.