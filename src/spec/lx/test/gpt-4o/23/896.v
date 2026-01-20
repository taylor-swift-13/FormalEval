Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_zz :
  Spec "zz" 2.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.