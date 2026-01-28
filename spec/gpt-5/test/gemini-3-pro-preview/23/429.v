Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen : strlen_spec "samplt1t" 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.