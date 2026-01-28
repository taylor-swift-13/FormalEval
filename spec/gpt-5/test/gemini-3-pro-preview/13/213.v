Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_234567888_234567888 : greatest_common_divisor_spec 234567888 234567888 234567888.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.