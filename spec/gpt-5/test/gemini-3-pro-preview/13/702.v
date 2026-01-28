Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_30_30 : greatest_common_divisor_spec 30 30 30.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.