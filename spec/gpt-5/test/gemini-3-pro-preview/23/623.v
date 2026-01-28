Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "   This is a sample string to test the function

   z" 53.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.