Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_3699635_3699635 : greatest_common_divisor_spec 3699635 3699635 3699635.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.