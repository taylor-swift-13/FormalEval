Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_ThTiTi : strlen_spec "ThTiTi" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.