Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_t1t : strlen_spec "t1t" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.