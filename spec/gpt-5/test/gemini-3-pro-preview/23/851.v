Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "   This is a sampleT stringunction

   z" 40.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.