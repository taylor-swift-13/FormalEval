Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_Qck : strlen_spec "Qck" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.