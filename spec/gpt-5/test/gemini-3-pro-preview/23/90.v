Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case1 : strlen_spec "one
twotaa
thrThis is a long string that has many characters ien itee
1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5four
five" 175.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.