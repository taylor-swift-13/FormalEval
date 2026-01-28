Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_TTBrownnnis : strlen_spec "TTBrownnnis   " 14.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.