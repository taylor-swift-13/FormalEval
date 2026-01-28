Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_wtestm5nTheymb0ls : strlen_spec "wtestm5nTheymb0ls" 17.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.