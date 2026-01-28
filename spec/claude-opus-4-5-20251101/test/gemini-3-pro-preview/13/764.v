Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_greatest_common_divisor_large : greatest_common_divisor_spec 123456790 1684168416838 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.