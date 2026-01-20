Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_nonempty :
  Spec "one\ntwot\nthree\nfour\nfive" 28.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.