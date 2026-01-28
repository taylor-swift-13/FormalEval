Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_TTBrown : strlen_spec "TTBrown" 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.