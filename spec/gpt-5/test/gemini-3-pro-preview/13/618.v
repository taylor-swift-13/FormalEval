Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_2516980251698_99999999 : greatest_common_divisor_spec 2516980251698 99999999 11.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.