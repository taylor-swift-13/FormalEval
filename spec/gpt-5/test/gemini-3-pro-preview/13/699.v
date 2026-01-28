Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_965_987654320 : greatest_common_divisor_spec 965 987654320 5.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.