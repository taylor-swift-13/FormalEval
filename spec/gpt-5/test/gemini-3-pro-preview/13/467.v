Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_100000005_420 : greatest_common_divisor_spec 100000005 420 105.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.