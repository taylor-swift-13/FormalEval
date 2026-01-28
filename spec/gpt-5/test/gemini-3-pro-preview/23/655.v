Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_ThTTi : strlen_spec "ThTTi" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.