Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_simple : strlen_spec "fux      ncc" 12.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.