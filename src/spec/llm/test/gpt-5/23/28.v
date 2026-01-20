Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_multiline: strlen_spec "one
twot
thrThis is a long string thtat has many characters in itee
four
five" 77.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_multiline_Z: Z.of_nat (String.length "one
twot
thrThis is a long string thtat has many characters in itee
four
five") = 77%Z.
Proof.
  simpl.
  reflexivity.
Qed.