Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_30_30 : greatest_common_divisor_spec 30 30 30.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.