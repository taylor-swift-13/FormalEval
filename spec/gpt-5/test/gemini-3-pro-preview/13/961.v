Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_123456790_111111111 : greatest_common_divisor_spec 123456790 111111111 12345679.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.