Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_ic : strlen_spec "ic" 2.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.