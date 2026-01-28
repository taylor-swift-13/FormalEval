Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_wwhyNcJH1thfunnchy1N : strlen_spec "wwhyNcJH1thfunnchy1N" 20.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.