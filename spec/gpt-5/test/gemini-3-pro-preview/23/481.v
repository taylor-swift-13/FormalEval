Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_wiiw1th : strlen_spec "wiiw1th" 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.