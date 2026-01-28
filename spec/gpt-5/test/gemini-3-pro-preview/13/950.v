Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_1684168416840_123456789 : greatest_common_divisor_spec 1684168416840 123456789 3.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.