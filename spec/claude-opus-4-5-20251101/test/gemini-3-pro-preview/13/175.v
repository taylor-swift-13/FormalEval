Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_1234567890_100000000 : greatest_common_divisor_spec 1234567890 100000000 10.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.