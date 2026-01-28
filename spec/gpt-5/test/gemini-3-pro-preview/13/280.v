Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_194_194 : greatest_common_divisor_spec 194 194 194.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.