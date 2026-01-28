Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_420_123456790 : greatest_common_divisor_spec 420 123456790 10.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.