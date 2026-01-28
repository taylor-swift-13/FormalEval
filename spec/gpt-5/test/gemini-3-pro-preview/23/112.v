Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_newlines : strlen_spec "   

   " 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.