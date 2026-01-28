Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_iw1th : strlen_spec "iw1th" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.