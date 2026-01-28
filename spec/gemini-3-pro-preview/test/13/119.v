Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_419_192 : greatest_common_divisor_spec 419 192 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.