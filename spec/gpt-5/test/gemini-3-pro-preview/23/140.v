Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_bang_n : strlen_spec "!n" 2.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.