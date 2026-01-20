Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "sTtTheTer1stgrsr1ngLqNCZAtestng" 31.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.