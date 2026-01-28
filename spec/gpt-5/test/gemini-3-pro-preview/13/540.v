Require Import ZArith.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b g : Z) : Prop :=
  Z.abs g = Z.gcd a b.

Example test_gcd_234567890_1684168416842 : greatest_common_divisor_spec 234567890 1684168416842 2.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.