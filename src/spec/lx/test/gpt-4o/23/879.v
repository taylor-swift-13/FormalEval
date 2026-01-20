Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_func_ontion :
  Spec "!func!ontion" 12.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.