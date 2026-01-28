Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec ("The quick brown fox jumps over theThe quick brown fox jxumps overq the lazy dog lazy Thisthree" ++ String (ascii_of_nat 10) ("four" ++ String (ascii_of_nat 10) "fiveracter dog")) 114.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.