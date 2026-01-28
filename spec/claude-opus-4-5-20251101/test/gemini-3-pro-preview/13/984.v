Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_234567889_100000000 : greatest_common_divisor_spec 234567889 100000000 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.