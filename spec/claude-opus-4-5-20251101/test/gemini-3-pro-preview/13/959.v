Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_100000000_2516980251699 : greatest_common_divisor_spec 100000000 2516980251699 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.