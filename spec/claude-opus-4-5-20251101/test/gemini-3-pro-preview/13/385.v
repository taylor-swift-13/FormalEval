Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_105_111111112 : greatest_common_divisor_spec 105 111111112 7.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.