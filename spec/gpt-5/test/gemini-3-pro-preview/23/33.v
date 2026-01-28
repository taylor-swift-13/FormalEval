Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_newline : strlen_spec "of
foive" 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.