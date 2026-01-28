Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_18_98765432100 : greatest_common_divisor_spec 18 98765432100 18.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.