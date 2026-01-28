Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_1000000001_100000005 : greatest_common_divisor_spec 1000000001 100000005 7.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.