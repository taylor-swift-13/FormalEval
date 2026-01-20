Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_234567887_3699638 : greatest_common_divisor_spec 234567887 3699638 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.