Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_234567892_234567892 : greatest_common_divisor_spec 234567892 234567892 234567892.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.