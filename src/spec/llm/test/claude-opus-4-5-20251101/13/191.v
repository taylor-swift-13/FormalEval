Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_234567890_234567890 : greatest_common_divisor_spec 234567890 234567890 234567890.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.