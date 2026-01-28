Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_k : strlen_spec "k" 1.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.