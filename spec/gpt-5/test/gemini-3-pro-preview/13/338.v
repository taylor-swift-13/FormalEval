Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_234567891_234567892 : greatest_common_divisor_spec 234567891 234567892 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.