Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_965_987654321 : greatest_common_divisor_spec 965 987654321 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.