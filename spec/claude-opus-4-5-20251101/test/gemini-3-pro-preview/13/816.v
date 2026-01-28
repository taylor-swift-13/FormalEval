Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_111111109_234567891 : greatest_common_divisor_spec 111111109 234567891 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.