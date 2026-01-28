Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_newline : strlen_spec "G1The quick brown f ox jumps over the lazy dog234  has a 
 newline character5NDKQyadEb" 86.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.