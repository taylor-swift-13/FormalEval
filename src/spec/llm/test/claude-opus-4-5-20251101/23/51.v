Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_long_string : strlen_spec "G1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5NDKQyadEb" 106.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.