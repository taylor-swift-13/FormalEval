Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_multiline :
  Spec "one\ntwo\nthree\nfour\nfive" 27.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.