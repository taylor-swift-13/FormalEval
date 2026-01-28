Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_44 : strlen_spec "44" 2.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.