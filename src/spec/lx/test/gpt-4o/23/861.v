Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_hCV :
  Spec "hCV" 3.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.