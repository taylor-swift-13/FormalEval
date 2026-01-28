Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_30_234567891 : greatest_common_divisor_spec 30 234567891 3.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.