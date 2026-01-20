Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "Tish!          This is a sample string    This is a sampl   unction4" 68.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.