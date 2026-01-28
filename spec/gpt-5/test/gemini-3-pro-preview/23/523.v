Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_custom : strlen_spec "striing     This is a sampl          tothe func tion          " 62.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.