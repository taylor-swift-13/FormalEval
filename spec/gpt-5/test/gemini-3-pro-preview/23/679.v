Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "MNhqThe CQuicJumpsk BrowMNhqmn Fox Jumps OverThis  to test t" 60.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.