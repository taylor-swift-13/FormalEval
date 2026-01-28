Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_967_111111109 : greatest_common_divisor_spec 967 111111109 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.