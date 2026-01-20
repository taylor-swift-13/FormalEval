Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_neg123457_neg12344 :
  multiply_spec_abs (-123457) (-12344) 28.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.