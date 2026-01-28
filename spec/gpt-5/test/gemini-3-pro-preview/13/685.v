Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_123456789_123456788 : greatest_common_divisor_spec 123456789 123456788 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.