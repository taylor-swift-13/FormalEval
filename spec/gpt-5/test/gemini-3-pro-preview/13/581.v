Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_98765432100_98765432098 : greatest_common_divisor_spec 98765432100 98765432098 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.