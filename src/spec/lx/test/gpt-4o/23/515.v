Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_whyNcJH1thFox :
  Spec "whyNcJH1thFox" 13.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.