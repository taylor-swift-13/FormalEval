Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_100000004_100000000 : greatest_common_divisor_spec 100000004 100000000 4.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.