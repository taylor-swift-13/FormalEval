Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_99999999_99999999 : greatest_common_divisor_spec 99999999 99999999 99999999.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.