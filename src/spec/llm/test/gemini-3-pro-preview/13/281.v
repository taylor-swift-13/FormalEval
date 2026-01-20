Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_234567887_123456788 : greatest_common_divisor_spec 234567887 123456788 17.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.