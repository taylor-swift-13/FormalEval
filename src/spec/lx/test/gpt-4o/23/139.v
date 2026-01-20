Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_Jummtops :
  Spec "Jummtops" 8.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.