Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "    This irs a sample string to tea  " 37.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.