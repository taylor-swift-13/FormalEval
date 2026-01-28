Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_rstr1ng : strlen_spec "rstr1ng" 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.