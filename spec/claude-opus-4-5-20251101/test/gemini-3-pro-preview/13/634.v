Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_108_987654320 : greatest_common_divisor_spec 108 987654320 4.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.