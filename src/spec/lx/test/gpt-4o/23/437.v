Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_FMcc :
  Spec "FMcc" 4.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.