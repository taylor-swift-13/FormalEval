Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_r1g :
  Spec "r1g" 3.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.