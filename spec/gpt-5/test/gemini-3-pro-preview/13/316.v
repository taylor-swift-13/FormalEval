Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_1000000001_234567888 : greatest_common_divisor_spec 1000000001 234567888 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.