Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_33_55 : greatest_common_divisor_spec 33 55 11.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.