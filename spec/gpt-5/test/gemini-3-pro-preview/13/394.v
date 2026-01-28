Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_98765432101_1684168416845 : greatest_common_divisor_spec 98765432101 1684168416845 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.