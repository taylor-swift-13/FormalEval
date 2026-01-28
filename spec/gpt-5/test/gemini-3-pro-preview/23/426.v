Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_str1nb0lse : strlen_spec "str1nb0lse" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.