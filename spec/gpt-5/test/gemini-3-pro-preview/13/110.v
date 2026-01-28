Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_999999999_111111111 : greatest_common_divisor_spec 999999999 111111111 111111111.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.