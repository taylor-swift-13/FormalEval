Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_3699638_111111110 : greatest_common_divisor_spec 3699638 111111110 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.