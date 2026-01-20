Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_neg99_1234567891 :
  multiply_spec_abs (-99) 1234567891 9.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.