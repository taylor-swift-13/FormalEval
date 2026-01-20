Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_21_35 : greatest_common_divisor_spec 21 35 7.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.