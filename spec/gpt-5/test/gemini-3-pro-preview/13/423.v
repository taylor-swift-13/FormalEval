Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_100000002_100000001 : greatest_common_divisor_spec 100000002 100000001 1.
Proof.
  unfold greatest_common_divisor_spec.
  compute.
  reflexivity.
Qed.