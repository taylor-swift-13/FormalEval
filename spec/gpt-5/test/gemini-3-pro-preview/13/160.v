Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_987654323_987654323 : greatest_common_divisor_spec 987654323 987654323 987654323.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.