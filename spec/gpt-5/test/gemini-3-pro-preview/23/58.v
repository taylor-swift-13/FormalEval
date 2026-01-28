Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "Hello, WoG1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5NDKThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazby Thisthree
four
fiveracter dogQyadEborlod!" 235.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.