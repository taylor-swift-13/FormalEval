Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_2147483647_2147483647 : greatest_common_divisor_spec 2147483647 2147483647 2147483647.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.