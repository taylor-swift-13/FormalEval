Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_whyNcJH1th : strlen_spec "whyNcJH1th" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.