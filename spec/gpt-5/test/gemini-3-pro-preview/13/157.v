Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_2516980251698_194 : greatest_common_divisor_spec 2516980251698 194 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.