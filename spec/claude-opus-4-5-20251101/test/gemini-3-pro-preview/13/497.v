Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_1000000001_9 : greatest_common_divisor_spec 1000000001 9 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.