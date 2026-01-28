Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1234567890 : strlen_spec "1234567890" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.