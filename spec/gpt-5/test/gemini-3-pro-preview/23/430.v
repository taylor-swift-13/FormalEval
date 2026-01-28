Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_wiw1s1th : strlen_spec "wiw1s1th" 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.