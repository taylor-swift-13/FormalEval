Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_111111112_1234567890 : greatest_common_divisor_spec 111111112 1234567890 2.
Proof.
  unfold greatest_common_divisor_spec.
  simpl.
  reflexivity.
Qed.