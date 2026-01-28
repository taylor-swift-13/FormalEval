Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_stricQukickn : strlen_spec "stricQukickn" 12.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.