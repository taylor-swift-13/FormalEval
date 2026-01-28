Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_234567891_999999999 : greatest_common_divisor_spec 234567891 999999999 9.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.