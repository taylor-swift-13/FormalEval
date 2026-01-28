Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_987654325_987654319 : greatest_common_divisor_spec 987654325 987654319 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.