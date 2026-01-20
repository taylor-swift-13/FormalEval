Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "    This is a sample strinitsg to test  the functiostgrsr1ngLqNCZAtestn          " 81.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.