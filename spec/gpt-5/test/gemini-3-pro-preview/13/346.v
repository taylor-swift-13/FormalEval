Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_12_98765432100 : greatest_common_divisor_spec 12 98765432100 12.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.