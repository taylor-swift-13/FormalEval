Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_long_string : strlen_spec "1234 This sitriThis is a long string that has many character12345s in itng has a 
 newline character5" 101.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.