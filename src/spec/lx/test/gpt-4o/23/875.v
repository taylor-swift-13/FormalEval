Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_non_empty :
  Spec "w1thTTBrownis" 13.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.