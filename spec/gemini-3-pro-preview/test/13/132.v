Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_419_1000000000 : greatest_common_divisor_spec 419 1000000000 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.