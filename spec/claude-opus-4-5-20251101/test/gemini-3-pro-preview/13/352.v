Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_107_2516980251698 : greatest_common_divisor_spec 107 2516980251698 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.