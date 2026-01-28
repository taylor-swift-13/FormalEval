Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_234567889_1684168416838 : greatest_common_divisor_spec 234567889 1684168416838 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.