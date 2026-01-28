Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen : strlen_spec "GThT    1t 1 The    ic" 22.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.