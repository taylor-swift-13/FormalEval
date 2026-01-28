Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_1684168416846_999999998 : greatest_common_divisor_spec 1684168416846 999999998 2.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.