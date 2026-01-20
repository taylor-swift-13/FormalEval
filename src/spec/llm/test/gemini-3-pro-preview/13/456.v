Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_3699639_3699639 : greatest_common_divisor_spec 3699639 3699639 3699639.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.