Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_100000001_106 : greatest_common_divisor_spec 100000001 106 1.
Proof.
  unfold greatest_common_divisor_spec.
  compute.
  reflexivity.
Qed.