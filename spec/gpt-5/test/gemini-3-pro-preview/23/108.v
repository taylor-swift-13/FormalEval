Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_sample : strlen_spec "This is a sample string to test the function" 44.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.