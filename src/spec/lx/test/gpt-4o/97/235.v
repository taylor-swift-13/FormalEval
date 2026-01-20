Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_neg987656_neg123457 :
  multiply_spec_abs (-987656) (-123457) 42.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.