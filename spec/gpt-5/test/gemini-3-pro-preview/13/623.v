Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_large : greatest_common_divisor_spec 98765432099 99999999 1.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.