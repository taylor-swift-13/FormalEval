Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "one
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

Example strlen_test_case_Z: Z.of_nat (String.length "one
twota
thrThis is a long string that has many chone
twot
thrThis is a long string that has  many characters in itee
four
fivearacters in itee
four
five") = 154%Z.
Proof.
  simpl.
  reflexivity.
Qed.