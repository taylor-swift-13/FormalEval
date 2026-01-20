Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_long_string : strlen_spec "one
twot This striThis is a long streing that has many characters in itng has a 
 newline character
three
four
five" 115.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.