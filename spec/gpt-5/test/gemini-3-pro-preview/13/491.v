Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_1684168416842_123456788 : greatest_common_divisor_spec 1684168416842 123456788 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.