Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen : strlen_spec "This sample string to      The     test the function" 52.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.