Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_98765432102_1684168416843 : greatest_common_divisor_spec 98765432102 1684168416843 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.