Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "The quick brown fox jumps overq theHello, World! lazy dog" 57.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.