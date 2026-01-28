Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_966_999999999 : greatest_common_divisor_spec 966 999999999 3.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.