Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_greatest_common_divisor : greatest_common_divisor_spec 1684168416845 98765432100 5.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.