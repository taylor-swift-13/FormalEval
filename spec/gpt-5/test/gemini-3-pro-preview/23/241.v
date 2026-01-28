Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_wiw1th : strlen_spec "wiw1th" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.