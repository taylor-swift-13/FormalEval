Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_Jumpsw1This : strlen_spec "Jumpsw1This" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.