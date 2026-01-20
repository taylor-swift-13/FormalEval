Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_do_the_g :
  Spec "Do      The    g" 16.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.