Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_108_966 : greatest_common_divisor_spec 108 966 6.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.