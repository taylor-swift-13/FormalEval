Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_wtest5nymb0ls : strlen_spec "wtest5nymb0ls" 13.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.