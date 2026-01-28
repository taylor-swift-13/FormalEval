Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_234567892_1684168416841 : greatest_common_divisor_spec 234567892 1684168416841 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.