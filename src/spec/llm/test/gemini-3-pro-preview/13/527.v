Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_194_195 : greatest_common_divisor_spec 194 195 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.