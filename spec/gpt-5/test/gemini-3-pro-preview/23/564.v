Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_st1r1n : strlen_spec "st1r1n" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.