Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_nonempty :
  Spec "Tish!whyNcJH1th          4" 26.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.