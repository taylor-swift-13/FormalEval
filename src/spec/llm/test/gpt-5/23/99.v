Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_multiline: strlen_spec "one
twota
thrThis is a long string that has many characters iThe quick bis striThis is aaracter dogMen itee
four
five" 117.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_multiline_Z: Z.of_nat (String.length "one
twota
thrThis is a long string that has many characters iThe quick bis striThis is aaracter dogMen itee
four
five") = 117%Z.
Proof.
  simpl.
  reflexivity.
Qed.