Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_long: strlen_spec "Testing te stingone
twot
thrThis is a long string that has many characters in itee
four
five 123" 96.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_long_Z: Z.of_nat (String.length "Testing te stingone
twot
thrThis is a long string that has many characters in itee
four
five 123") = 96%Z.
Proof.
  simpl.
  reflexivity.
Qed.