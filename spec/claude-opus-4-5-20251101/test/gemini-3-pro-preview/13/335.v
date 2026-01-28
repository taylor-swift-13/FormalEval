Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_11_11 : greatest_common_divisor_spec 11 11 11.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.