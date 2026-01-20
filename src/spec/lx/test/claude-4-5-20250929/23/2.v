Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_single_char :
  Spec "x" 1.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.