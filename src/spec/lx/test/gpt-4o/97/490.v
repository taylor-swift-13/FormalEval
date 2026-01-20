Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_minus12348_minus16 :
  multiply_spec_abs (-12348) (-16) 48.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.