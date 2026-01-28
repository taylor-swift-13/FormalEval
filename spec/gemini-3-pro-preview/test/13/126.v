Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_3699637_3699637 : greatest_common_divisor_spec 3699637 3699637 3699637.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.