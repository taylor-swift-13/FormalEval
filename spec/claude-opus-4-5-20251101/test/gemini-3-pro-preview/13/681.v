Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_111111110_1000000000 : greatest_common_divisor_spec 111111110 1000000000 10.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.