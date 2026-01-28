Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_FMc : strlen_spec "FMc" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.