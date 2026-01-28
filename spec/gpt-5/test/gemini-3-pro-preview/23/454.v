Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_fuwhy1N : strlen_spec "fuwhy1N" 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.