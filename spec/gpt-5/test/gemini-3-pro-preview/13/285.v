Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_987654320_1000000000 : greatest_common_divisor_spec 987654320 1000000000 80.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.