Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_hello_world : strlen_spec "Hello, World!" 13.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.