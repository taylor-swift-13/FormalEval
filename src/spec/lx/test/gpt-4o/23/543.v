Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_nonempty :
  Spec "stgrsr1ngLqNtCZAtest" 20.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.