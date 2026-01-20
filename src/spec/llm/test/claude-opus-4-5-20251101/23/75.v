Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_long_string : strlen_spec "one
twota
thrThis is a long string that has many chone
twot
thrThis is a long string that has  many characters in itee
four
fivearacters in itee
four
five" 154.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.