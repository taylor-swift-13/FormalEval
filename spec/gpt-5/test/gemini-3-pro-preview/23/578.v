Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_rstn1r1n : strlen_spec "rstn1r1n" 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.