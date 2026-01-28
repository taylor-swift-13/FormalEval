Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_p1sBrown : strlen_spec "p1sBrown" 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.