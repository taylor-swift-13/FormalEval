Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_30_98765432101 : greatest_common_divisor_spec 30 98765432101 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.