Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_99999999_987654320 : greatest_common_divisor_spec 99999999 987654320 1.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.