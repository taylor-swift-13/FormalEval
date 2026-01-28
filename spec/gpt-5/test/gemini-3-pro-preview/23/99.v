Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "one
twota
thrThis is a long string that has many characters iThe quick bis striThis is aaracter dogMen itee
four
five" 117.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.