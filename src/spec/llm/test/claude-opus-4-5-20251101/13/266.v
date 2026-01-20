Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_111111112_111111111 : greatest_common_divisor_spec 111111112 111111111 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.