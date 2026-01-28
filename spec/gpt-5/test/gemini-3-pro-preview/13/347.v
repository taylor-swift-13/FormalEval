Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_111111111_100000000 : greatest_common_divisor_spec 111111111 100000000 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.