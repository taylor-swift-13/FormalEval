Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_2516980251698_194 : greatest_common_divisor_spec 2516980251698 194 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.