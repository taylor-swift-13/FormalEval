Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_RLkion : strlen_spec "RLkion" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.