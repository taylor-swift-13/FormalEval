Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_123456788_195 : greatest_common_divisor_spec 123456788 195 13.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.