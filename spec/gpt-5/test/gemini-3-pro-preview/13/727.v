Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_999999998_234567890 : greatest_common_divisor_spec 999999998 234567890 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.