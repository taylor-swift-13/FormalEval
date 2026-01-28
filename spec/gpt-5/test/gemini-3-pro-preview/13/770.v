Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_3699636_420 : greatest_common_divisor_spec 3699636 420 12.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.