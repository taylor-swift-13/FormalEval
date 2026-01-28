Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_iwTish1th : strlen_spec "iwTish!1th" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.