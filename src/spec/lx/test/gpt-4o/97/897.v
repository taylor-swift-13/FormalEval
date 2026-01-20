Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_neg123457_neg12345 :
  multiply_spec_abs (-123457) (-12345) 35.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.