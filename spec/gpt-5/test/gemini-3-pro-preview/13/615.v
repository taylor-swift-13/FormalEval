Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_99999999_966 : greatest_common_divisor_spec 99999999 966 3.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.