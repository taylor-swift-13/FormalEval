Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_long_string_with_newline : strlen_spec " This striThis is a long string that has many characters in itng has a 
 newline character" 90.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.