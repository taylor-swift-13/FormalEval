Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_large : greatest_common_divisor_spec 98765432100 111111111 9.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.