Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_long: strlen_spec "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789" 99.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_long_Z: Z.of_nat (String.length "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789") = 99%Z.
Proof.
  simpl.
  reflexivity.
Qed.