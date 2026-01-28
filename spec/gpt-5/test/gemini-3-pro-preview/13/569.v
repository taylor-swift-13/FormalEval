Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_98765432101_987654318 : greatest_common_divisor_spec 98765432101 987654318 7.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.