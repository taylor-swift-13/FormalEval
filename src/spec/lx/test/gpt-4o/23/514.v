Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_wtest5nymb0ls :
  Spec "wtest5nymb0ls" 13.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.