Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_234567890_100000000 : greatest_common_divisor_spec 234567890 100000000 10.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.