Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "ywwtensLazy    This is a samQuaOverickple TTetnstrinisg to test the function           " 87.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.