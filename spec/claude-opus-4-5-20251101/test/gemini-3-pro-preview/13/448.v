Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_98765432098_98765432098 : greatest_common_divisor_spec 98765432098 98765432098 98765432098.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.