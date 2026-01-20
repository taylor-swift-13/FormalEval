Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_nonempty :
  Spec "fJumpeuon" 9.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.