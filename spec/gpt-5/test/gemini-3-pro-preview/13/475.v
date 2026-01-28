Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_1000000000_2516980251698 : greatest_common_divisor_spec 1000000000 2516980251698 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.