Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_mixed : strlen_spec "Th!s 1s 4 str1str1 1t" 21.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.