Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_aaa : strlen_spec "aaa" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.