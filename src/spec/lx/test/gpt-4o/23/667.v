Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_overthis :
  Spec "OverThis" 8.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.