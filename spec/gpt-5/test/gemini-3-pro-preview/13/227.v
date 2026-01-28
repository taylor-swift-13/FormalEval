Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_98765432100_1000000000 : greatest_common_divisor_spec 98765432100 1000000000 100.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.