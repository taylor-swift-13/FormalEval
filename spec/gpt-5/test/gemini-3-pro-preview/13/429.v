Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_123456790_123456790 : greatest_common_divisor_spec 123456790 123456790 123456790.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.