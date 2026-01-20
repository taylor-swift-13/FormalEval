Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_complex :
  Spec "te      1t  sThe    s tt" 24.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.