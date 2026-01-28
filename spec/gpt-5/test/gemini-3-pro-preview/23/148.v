Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "Fo    This is a sampleto string to test the function  n        x" 64.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.