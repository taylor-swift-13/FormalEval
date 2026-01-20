Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_long_string : strlen_spec "Hello, WoG1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5NDKThe quick brown fox jumps over theThe quick by Thisthree
four
fiveracter dogQyadEborlod!" 197.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.