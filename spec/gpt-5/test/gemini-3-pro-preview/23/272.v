Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_fux : strlen_spec "fux" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.