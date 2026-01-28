Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_54_9 : greatest_common_divisor_spec 54 9 9.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.