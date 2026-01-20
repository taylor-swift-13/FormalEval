Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_empty :
  Spec "" 0.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.