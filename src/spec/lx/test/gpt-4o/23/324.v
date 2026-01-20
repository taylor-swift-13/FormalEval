Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_nonempty :
  Spec "wwhyNcJH1thfunnchy1N" 20.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.