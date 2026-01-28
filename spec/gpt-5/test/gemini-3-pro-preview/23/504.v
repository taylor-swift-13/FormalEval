Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen : strlen_spec "string4cJH1Jth" 14.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.