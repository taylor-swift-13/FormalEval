Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_4_n : strlen_spec "4!n" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.