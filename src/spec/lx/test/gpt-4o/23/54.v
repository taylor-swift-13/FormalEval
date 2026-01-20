Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_oef_ffoive :
  Spec "oef
ffoive" 10.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.