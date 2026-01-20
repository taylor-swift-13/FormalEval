Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_nonempty :
  Spec "rrstr1ng" 8.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.