Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_funnc :
  Spec "funnc" 5.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.