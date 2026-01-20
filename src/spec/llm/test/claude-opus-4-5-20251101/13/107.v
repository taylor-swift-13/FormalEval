Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_234567890_987654321 : greatest_common_divisor_spec 234567890 987654321 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.