Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_987654320_111111111 : greatest_common_divisor_spec 987654320 111111111 12345679.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.