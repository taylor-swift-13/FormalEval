Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_194_987654322 : greatest_common_divisor_spec 194 987654322 2.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.