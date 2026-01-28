Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_99999999_3699636 : greatest_common_divisor_spec 99999999 3699636 3.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.