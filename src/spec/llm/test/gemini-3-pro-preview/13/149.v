Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_234567889_234567890 : greatest_common_divisor_spec 234567889 234567890 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.