Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_non_empty :
  Spec "The Quick Brown Fox Jumpe Lazy Dog" 34.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.