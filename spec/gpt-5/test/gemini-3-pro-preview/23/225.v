Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_astr1ngsampl : strlen_spec "astr1ngsampl" 12.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.