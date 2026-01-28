Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_50_98765432101 : greatest_common_divisor_spec 50 98765432101 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.