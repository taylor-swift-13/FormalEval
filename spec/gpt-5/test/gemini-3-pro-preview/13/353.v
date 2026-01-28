Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_1000000000_100000000 : greatest_common_divisor_spec 1000000000 100000000 100000000.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.