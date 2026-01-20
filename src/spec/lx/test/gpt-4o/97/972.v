Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_neg_123457_neg_123456 :
  multiply_spec_abs (-123457) (-123456) 42.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.