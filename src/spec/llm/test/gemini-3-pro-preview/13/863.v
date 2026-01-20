Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_28_2516980251698 : greatest_common_divisor_spec 28 2516980251698 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.