Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_3699639_999999999 : greatest_common_divisor_spec 3699639 999999999 9.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.