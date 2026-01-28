Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_987654324_987654320 : greatest_common_divisor_spec 987654324 987654320 4.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.