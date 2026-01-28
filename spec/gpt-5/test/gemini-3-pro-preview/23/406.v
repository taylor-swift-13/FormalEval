Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_str1ngsampaOverl : strlen_spec "str1ngsampaOverl" 16.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.