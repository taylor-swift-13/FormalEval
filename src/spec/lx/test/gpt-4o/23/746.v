Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_rstr1ng :
  Spec "rstr1ng" 7.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.