Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_Brow : strlen_spec "Brow" 4.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.