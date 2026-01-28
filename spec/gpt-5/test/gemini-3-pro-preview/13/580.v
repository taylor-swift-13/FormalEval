Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_111111109_100000005 : greatest_common_divisor_spec 111111109 100000005 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.