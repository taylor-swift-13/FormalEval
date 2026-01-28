Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_funthstr1ng : strlen_spec "funthstr1ng" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.