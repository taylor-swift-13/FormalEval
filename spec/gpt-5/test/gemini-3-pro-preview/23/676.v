Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_functont : strlen_spec "functont" 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.