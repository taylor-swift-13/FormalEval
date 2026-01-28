Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_99999999_234567890 : greatest_common_divisor_spec 99999999 234567890 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.