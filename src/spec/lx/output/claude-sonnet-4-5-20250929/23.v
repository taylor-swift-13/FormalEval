Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_empty :
  Spec EmptyString 0.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.