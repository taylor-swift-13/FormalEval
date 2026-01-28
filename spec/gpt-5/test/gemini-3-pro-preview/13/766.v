Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_987654320_987654318 : greatest_common_divisor_spec 987654320 987654318 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.