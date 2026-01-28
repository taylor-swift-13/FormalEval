Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "te      1t  sThe    s tt" 24.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.