Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_example : strlen_spec "  ring to tea  " 15.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.