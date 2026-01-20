Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_QGLWea :
  Spec "QGLWea" 6.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.